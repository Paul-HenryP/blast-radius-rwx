import ast
import builtins
import concurrent.futures
import glob
import gzip
import importlib
import importlib.abc
import importlib.machinery
import io
import json
import multiprocessing
import os
import pickle
import re
import signal
import sys
import time
import unittest
from collections import defaultdict
from pathlib import Path

try:
    import resource
except ImportError:
    resource = None

SRC_DIR = Path(__file__).resolve().parent
REPO_ROOT = Path("/app/sqlglot") if Path("/app/sqlglot").exists() else Path("sqlglot").resolve()

# Calibrated EV parameters (realistic fork/import overhead + CPU speed vs CI workers)
LIVE_SINGLE_MAX_S = 7.0
LIVE_COMMIT_MAX_S = 18.0
LIVE_FIXED_OVERHEAD_S = 0.70
LIVE_SPEED_FACTOR = 0.90
LIVE_EV_THRESHOLD = 0.90
TOTAL_LIVE_BUDGET_S = 95.0

PEP263_RE = re.compile(r"coding[:=]\s*[-\w.]+")

NEVER_DROP_LIVE_IDS = {
    "tests/dialects/test_dialect.py::TestDialect::test_lazy_load",
}
NEVER_DROP_LIVE_FILES = {
    "tests/test_dialect_imports.py",
    "tests/test_dialect_entry_points.py",
    "tests/test_build.py",
    "tests/test_sqlglotc.py",
}


def parse_patch(patch_path):
    files = {}
    cur = None
    cur_old_line = 0
    old_path = None
    with open(patch_path, "r", encoding="utf-8", errors="ignore") as f:
        for raw in f:
            line = raw.rstrip("\r\n")
            if line.startswith("--- "):
                old_path = line[4:].strip()
                if old_path.startswith("a/"):
                    old_path = old_path[2:]
            elif line.startswith("+++ "):
                new_path = line[4:].strip()
                if new_path.startswith("b/"):
                    new_path = new_path[2:]
                rel = new_path if new_path != "/dev/null" else old_path
                cur = rel
                files[cur] = {
                    "old_lines": set(),
                    "is_new": old_path == "/dev/null",
                    "is_del": new_path == "/dev/null",
                    "hunks": [],
                }
            elif line.startswith("@@ ") and cur is not None:
                m = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", line)
                if m:
                    o_start = int(m.group(1))
                    o_cnt = int(m.group(2)) if m.group(2) is not None else 1
                    n_start = int(m.group(3))
                    n_cnt = int(m.group(4)) if m.group(4) is not None else 1
                    cur_old_line = o_start
                    files[cur]["hunks"].append([o_start, o_cnt, n_start, n_cnt, []])
            elif cur is not None and files[cur]["hunks"]:
                if line.startswith("\\"):
                    continue
                if line == "":
                    line = " "
                files[cur]["hunks"][-1][4].append(line)
                if line.startswith("-"):
                    files[cur]["old_lines"].add(cur_old_line)
                    cur_old_line += 1
                elif line.startswith("+"):
                    prev_h = files[cur]["hunks"][-1][4]
                    if len(prev_h) < 2 or not prev_h[-2].startswith("-"):
                        files[cur]["old_lines"].add(max(1, cur_old_line - 1))
                        files[cur]["old_lines"].add(cur_old_line)
                elif line.startswith(" "):
                    cur_old_line += 1
    return files


def apply_hunks(old_text, hunks):
    old_lines = old_text.splitlines(keepends=False)
    out = []
    idx = 0
    for o_start, o_cnt, n_start, n_cnt, hlines in hunks:
        target = max(0, o_start - 1) if o_cnt > 0 else o_start
        out.extend(old_lines[idx:target])
        idx = target
        for hl in hlines:
            if hl.startswith(" ") or hl == "":
                out.append(old_lines[idx] if idx < len(old_lines) else hl[1:])
                idx += 1
            elif hl.startswith("-"):
                idx += 1
            elif hl.startswith("+"):
                out.append(hl[1:])
    out.extend(old_lines[idx:])
    return "\n".join(out) + ("\n" if old_text.endswith("\n") else "")


_AST_CACHE = {}


def _get_old_ast(rel_file):
    if rel_file not in _AST_CACHE:
        p = REPO_ROOT / rel_file
        if not p.exists():
            _AST_CACHE[rel_file] = (None, None)
        else:
            txt = p.read_text(encoding="utf-8", errors="ignore")
            try:
                tree = ast.parse(txt)
            except SyntaxError:
                tree = None
            _AST_CACHE[rel_file] = (txt, tree)
    return _AST_CACHE[rel_file]


def _diff_expr_for_lambdas(o_node, n_node, changed_lambdas):
    """Return True if any non-Lambda-body difference exists between two AST subtrees."""
    if type(o_node) is not type(n_node):
        return True
    if not isinstance(o_node, ast.AST):
        if isinstance(o_node, list):
            if len(o_node) != len(n_node):
                return True
            for x, y in zip(o_node, n_node):
                if _diff_expr_for_lambdas(x, y, changed_lambdas):
                    return True
            return False
        return o_node != n_node
    if ast.dump(o_node, include_attributes=False) == ast.dump(n_node, include_attributes=False):
        return False
    if isinstance(o_node, ast.Lambda):
        if ast.dump(o_node.args, include_attributes=False) != ast.dump(n_node.args, include_attributes=False):
            return True
        changed_lambdas.add(o_node.lineno)
        return False
    for field in o_node._fields:
        if _diff_expr_for_lambdas(getattr(o_node, field), getattr(n_node, field), changed_lambdas):
            return True
    return False


def _diff_ast_body(old_body, new_body, changed_def_linenos):
    if len(old_body) != len(new_body):
        return True
    for o_stmt, n_stmt in zip(old_body, new_body):
        if type(o_stmt) is not type(n_stmt):
            return True
        if isinstance(o_stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if o_stmt.name != n_stmt.name:
                return True
            if ast.dump(o_stmt, include_attributes=False) == ast.dump(n_stmt, include_attributes=False):
                continue
            if (
                ast.dump(o_stmt.args, include_attributes=False) != ast.dump(n_stmt.args, include_attributes=False)
                or len(o_stmt.decorator_list) != len(n_stmt.decorator_list)
                or any(
                    ast.dump(d1, include_attributes=False) != ast.dump(d2, include_attributes=False)
                    for d1, d2 in zip(o_stmt.decorator_list, n_stmt.decorator_list)
                )
                or (ast.dump(o_stmt.returns, include_attributes=False) if o_stmt.returns else None)
                != (ast.dump(n_stmt.returns, include_attributes=False) if n_stmt.returns else None)
            ):
                return True
            changed_def_linenos.add(o_stmt.lineno)
        elif isinstance(o_stmt, ast.ClassDef):
            if o_stmt.name != n_stmt.name:
                return True
            if ast.dump(o_stmt, include_attributes=False) == ast.dump(n_stmt, include_attributes=False):
                continue
            if (
                len(o_stmt.bases) != len(n_stmt.bases)
                or any(
                    ast.dump(b1, include_attributes=False) != ast.dump(b2, include_attributes=False)
                    for b1, b2 in zip(o_stmt.bases, n_stmt.bases)
                )
                or len(o_stmt.keywords) != len(n_stmt.keywords)
                or any(
                    ast.dump(k1, include_attributes=False) != ast.dump(k2, include_attributes=False)
                    for k1, k2 in zip(o_stmt.keywords, n_stmt.keywords)
                )
                or len(o_stmt.decorator_list) != len(n_stmt.decorator_list)
                or any(
                    ast.dump(d1, include_attributes=False) != ast.dump(d2, include_attributes=False)
                    for d1, d2 in zip(o_stmt.decorator_list, n_stmt.decorator_list)
                )
            ):
                return True
            if _diff_ast_body(o_stmt.body, n_stmt.body, changed_def_linenos):
                return True
        else:
            if ast.dump(o_stmt, include_attributes=False) != ast.dump(n_stmt, include_attributes=False):
                # Allow edits that ONLY change the body of a lambda (e.g., parser/generator FUNCTIONS/TRANSFORMS dicts)
                lambdas = set()
                if not _diff_expr_for_lambdas(o_stmt, n_stmt, lambdas) and lambdas:
                    changed_def_linenos.update(lambdas)
                else:
                    return True
    return False


def _changed_top_classes(old_ast, new_ast):
    if len(old_ast.body) != len(new_ast.body):
        return None
    changed = []
    for o, n in zip(old_ast.body, new_ast.body):
        if type(o) is not type(n):
            return None
        if ast.dump(o, include_attributes=False) == ast.dump(n, include_attributes=False):
            continue
        if isinstance(o, ast.ClassDef) and o.name == n.name:
            changed.append((o, n))
        else:
            return None
    return changed


def _dialect_component_only(changed_class_pairs):
    comp_map = {"Tokenizer": "tok_files", "Parser": "par_files", "Generator": "gen_files"}
    components = set()
    for o_cls, n_cls in changed_class_pairs:
        if len(o_cls.body) != len(n_cls.body):
            return None
        for o_s, n_s in zip(o_cls.body, n_cls.body):
            if type(o_s) is not type(n_s):
                return None
            if ast.dump(o_s, include_attributes=False) == ast.dump(n_s, include_attributes=False):
                continue
            if isinstance(o_s, ast.ClassDef) and o_s.name == n_s.name and o_s.name in comp_map:
                components.add(comp_map[o_s.name])
            else:
                return None
    return components if components else None


def _stmt_lines_lookup(cfile, old_ast, old_lines, file_lines_map, tm_funcs, idxs_to_nums):
    """Map changed lines inside function/lambda bodies to enclosing statement entry lines."""
    if not file_lines_map or not old_lines:
        return set(), False

    all_stmts = []
    all_lambdas = []
    for node in ast.walk(old_ast):
        if isinstance(node, ast.Lambda):
            start = getattr(node, "lineno", None)
            end = getattr(node, "end_lineno", start)
            if start is not None:
                all_lambdas.append((end - start, start, end, node))
        elif isinstance(node, ast.stmt) and not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            start = getattr(node, "lineno", None)
            end = getattr(node, "end_lineno", start)
            if start is not None:
                all_stmts.append((end - start, start, end, node))

    selected_nums = set()
    for ln in old_lines:
        # Prefer enclosing Lambda if edit is inside a lambda expression
        lam_enc = [s for s in all_lambdas if s[1] <= ln <= s[2]]
        if lam_enc:
            lam_enc.sort(key=lambda x: x[0])
            _, l_start, l_end, _ = lam_enc[0]
            fkey = f"{cfile}:{l_start}"
            if fkey in tm_funcs:
                selected_nums.update(idxs_to_nums(tm_funcs[fkey]))
                continue
            return set(), False

        enclosing = [s for s in all_stmts if s[1] <= ln <= s[2]]
        if not enclosing:
            return set(), False
        enclosing.sort(key=lambda x: x[0])
        _, s_start, s_end, s_node = enclosing[0]

        body = getattr(s_node, "body", None)
        if body:
            h_end = max(s_start, min(getattr(body[0], "lineno", s_end) - 1, s_end))
            search_range = range(s_start, h_end + 1) if ln <= h_end else range(ln, ln + 1)
        else:
            search_range = range(s_start, s_end + 1)

        hit = set()
        for cand_ln in search_range:
            k = str(cand_ln)
            if k in file_lines_map:
                hit.update(idxs_to_nums(file_lines_map[k]))
                break
        if str(ln) in file_lines_map:
            hit.update(idxs_to_nums(file_lines_map[str(ln)]))

        if not hit:
            for cand_ln in search_range:
                k = str(cand_ln)
                if k in file_lines_map:
                    hit.update(idxs_to_nums(file_lines_map[k]))
        if not hit:
            return set(), False
        selected_nums.update(hit)

    return selected_nums, bool(selected_nums)



SAFE_NONE_TYPES = {
    "None", "bool", "int", "float", "str", "bytes", "list", "dict", "set", "frozenset", "tuple",
    "Sequence", "Mapping", "Iterable", "Iterator", "Callable", "type", "Type", "Path",
    "Table", "Expr", "Expression", "Dialect", "DialectType", "Token", "TokenType", "Tokenizer",
    "Parser", "Generator", "Scope", "Schema", "MappingSchema", "Step", "Plan", "Node", "Context",
    "NormalizationStrategy", "ErrorLevel", "DataType", "TypeAnnotator", "Keep", "KeepType",
    "Journal", "Diff", "Action", "ScopeType", "JoinHint", "Window", "Select", "Union", "Subquery",
}
UNSAFE_NONE_TYPES = {"Any", "object", "reverse_key", "ndarray", "NDArray", "DataFrame", "Series", "Mock", "MagicMock"}
_IMPORT_TIME_ATTRS_CACHE = None
_ENUM_INFO_CACHE = {}


def _file_imports_unsafe_eq(old_ast):
    for node in ast.walk(old_ast):
        if isinstance(node, ast.Import):
            for a in node.names:
                root = a.name.split(".")[0]
                if root in ("numpy", "pandas", "unittest"):
                    return True
        elif isinstance(node, ast.ImportFrom) and node.module:
            root = node.module.split(".")[0]
            if root in ("numpy", "pandas"):
                return True
    return False


def _ann_is_safe_for_none(ann):
    if ann is None:
        return False
    if isinstance(ann, ast.Constant):
        if ann.value is None:
            return True
        if isinstance(ann.value, str):
            try:
                return _ann_is_safe_for_none(ast.parse(ann.value, mode="eval").body)
            except SyntaxError:
                return False
        return False
    if isinstance(ann, ast.Name):
        return ann.id in SAFE_NONE_TYPES and ann.id not in UNSAFE_NONE_TYPES
    if isinstance(ann, ast.Attribute):
        if ann.attr in UNSAFE_NONE_TYPES:
            return False
        if isinstance(ann.value, ast.Name) and ann.value.id in ("exp", "expressions", "t", "typing"):
            return ann.attr not in UNSAFE_NONE_TYPES and (ann.attr in SAFE_NONE_TYPES or ann.attr[:1].isupper())
        return ann.attr in SAFE_NONE_TYPES
    if isinstance(ann, ast.BinOp) and isinstance(ann.op, ast.BitOr):
        return _ann_is_safe_for_none(ann.left) and _ann_is_safe_for_none(ann.right)
    if isinstance(ann, ast.Subscript):
        base = ann.value
        base_name = base.attr if isinstance(base, ast.Attribute) else (base.id if isinstance(base, ast.Name) else "")
        if base_name in ("Optional", "Union", "ClassVar", "Final"):
            sl = ann.slice
            if isinstance(sl, ast.Tuple):
                return all(_ann_is_safe_for_none(e) for e in sl.elts)
            return _ann_is_safe_for_none(sl)
        if base_name in ("list", "List", "dict", "Dict", "set", "Set", "frozenset", "FrozenSet", "tuple", "Tuple", "Sequence", "Mapping", "Iterable"):
            return True
        return False
    return False


def _collect_safe_none_targets(cls_node, func_node):
    safe_vars = set()
    safe_self_attrs = set()
    if func_node is not None:
        args = func_node.args
        for a in list(args.posonlyargs) + list(args.args) + list(args.kwonlyargs):
            if _ann_is_safe_for_none(a.annotation):
                safe_vars.add(a.arg)
        for n in ast.walk(func_node):
            if isinstance(n, ast.AnnAssign) and _ann_is_safe_for_none(n.annotation):
                if isinstance(n.target, ast.Name):
                    safe_vars.add(n.target.id)
                elif isinstance(n.target, ast.Attribute) and isinstance(n.target.value, ast.Name) and n.target.value.id == "self":
                    safe_self_attrs.add(n.target.attr)
    if cls_node is not None:
        for item in cls_node.body:
            if isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name) and _ann_is_safe_for_none(item.annotation):
                safe_self_attrs.add(item.target.id)
            elif isinstance(item, ast.FunctionDef) and item.name == "__init__":
                for n in ast.walk(item):
                    if isinstance(n, ast.AnnAssign) and _ann_is_safe_for_none(n.annotation):
                        if isinstance(n.target, ast.Attribute) and isinstance(n.target.value, ast.Name) and n.target.value.id == "self":
                            safe_self_attrs.add(n.target.attr)
    return safe_vars, safe_self_attrs


def _enum_class_kind(cls_name, old_ast):
    """Return 'pure' (non-str/int Enum), 'mixin' (str/int Enum), or None."""
    if cls_name in _ENUM_INFO_CACHE:
        return _ENUM_INFO_CACHE[cls_name]
    trees = [old_ast]
    for node in old_ast.body:
        if isinstance(node, ast.ImportFrom) and node.module and node.module.startswith("sqlglot"):
            if any(a.name == cls_name or a.asname == cls_name for a in node.names):
                mod_rel = node.module.replace(".", "/") + ".py"
                _, mt = _get_old_ast(mod_rel)
                if mt is not None:
                    trees.append(mt)
    kind = None
    for t_ast in trees:
        for node in t_ast.body:
            if isinstance(node, ast.ClassDef) and node.name == cls_name:
                bnames = {
                    (b.attr if isinstance(b, ast.Attribute) else (b.id if isinstance(b, ast.Name) else ""))
                    for b in node.bases
                }
                if bnames & {"Enum", "AutoName", "IntEnum", "StrEnum"}:
                    if bnames & {"str", "int", "float", "bytes", "IntEnum", "StrEnum"}:
                        kind = "mixin"
                    else:
                        kind = "pure"
                    break
        if kind is not None:
            break
    _ENUM_INFO_CACHE[cls_name] = kind
    return kind


def _self_attr_only_assigned_enum(attr_name, enum_name, cls_node):
    if cls_node is None:
        return False
    class_const_ok = set()
    for stmt in cls_node.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            val = stmt.value
            if isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id == enum_name:
                class_const_ok.add(stmt.targets[0].id)
        elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name) and stmt.value is not None:
            val = stmt.value
            if isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id == enum_name:
                class_const_ok.add(stmt.target.id)

    assigned = 0
    for node in ast.walk(cls_node):
        val = None
        if isinstance(node, ast.Assign):
            if any(isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == "self" and t.attr == attr_name for t in node.targets):
                val = node.value
        elif isinstance(node, ast.AnnAssign):
            t = node.target
            if isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == "self" and t.attr == attr_name:
                val = node.value
        if val is None:
            continue
        assigned += 1
        ok = False
        if isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == enum_name:
            ok = True
        elif isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id == enum_name:
            ok = True
        elif isinstance(val, ast.Attribute) and isinstance(val.value, ast.Name) and val.value.id == "self" and val.attr in class_const_ok:
            ok = True
        if not ok:
            return False
    return assigned > 0


def _is_safe_identity_eq(cmp_node, cls_node, func_node, old_ast, unsafe_imports):
    if unsafe_imports or len(cmp_node.ops) != 1 or len(cmp_node.comparators) != 1:
        return False
    left, right = cmp_node.left, cmp_node.comparators[0]
    for target, other in ((right, left), (left, right)):
        if isinstance(target, ast.Constant) and target.value is None:
            safe_vars, safe_self_attrs = _collect_safe_none_targets(cls_node, func_node)
            if isinstance(other, ast.Name) and other.id in safe_vars:
                return True
            if isinstance(other, ast.Attribute) and isinstance(other.value, ast.Name) and other.value.id == "self" and other.attr in safe_self_attrs:
                return True
        elif isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) and target.value.id[:1].isupper() and target.attr.isupper():
            enum_name = target.value.id
            ekind = _enum_class_kind(enum_name, old_ast)
            if ekind == "pure":
                safe_vars, safe_self_attrs = _collect_safe_none_targets(cls_node, func_node)
                if isinstance(other, ast.Name) and other.id in safe_vars:
                    return True
                if isinstance(other, ast.Attribute) and isinstance(other.value, ast.Name) and other.value.id == "self" and other.attr in safe_self_attrs:
                    return True
            elif ekind == "mixin":
                if isinstance(other, ast.Attribute) and isinstance(other.value, ast.Name) and other.value.id == "self":
                    if _self_attr_only_assigned_enum(other.attr, enum_name, cls_node):
                        return True
    return False


def _is_semantically_equivalent_ast(old_ast, new_ast):
    """Return True iff all AST differences are provably safe is/== or is not/!= swaps."""
    unsafe_imports = _file_imports_unsafe_eq(old_ast)
    swap_pairs = {(ast.Is, ast.Eq), (ast.Eq, ast.Is), (ast.IsNot, ast.NotEq), (ast.NotEq, ast.IsNot)}
    found_swap = False

    def _walk(o, n, cls_node, func_node):
        nonlocal found_swap
        if type(o) is not type(n):
            return False
        if not isinstance(o, ast.AST):
            if isinstance(o, list):
                if len(o) != len(n):
                    return False
                return all(_walk(x, y, cls_node, func_node) for x, y in zip(o, n))
            return o == n
        if ast.dump(o, include_attributes=False) == ast.dump(n, include_attributes=False):
            return True
        if isinstance(o, ast.ClassDef):
            cls_node = o
        elif isinstance(o, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_node = o
        elif isinstance(o, ast.Compare) and len(o.ops) == 1 and len(n.ops) == 1 and len(o.comparators) == 1 and len(n.comparators) == 1:
            if (type(o.ops[0]), type(n.ops[0])) in swap_pairs:
                if (
                    ast.dump(o.left, include_attributes=False) == ast.dump(n.left, include_attributes=False)
                    and ast.dump(o.comparators[0], include_attributes=False) == ast.dump(n.comparators[0], include_attributes=False)
                    and _is_safe_identity_eq(o, cls_node, func_node, old_ast, unsafe_imports)
                ):
                    found_swap = True
                    return True
                return False
        for field in o._fields:
            if not _walk(getattr(o, field), getattr(n, field), cls_node, func_node):
                return False
        return True

    return _walk(old_ast, new_ast, None, None) and found_swap


def _changed_all_caps_class_attrs(changed_class_pairs):
    """If class edits ONLY change RHS of existing ALL_CAPS class attributes, return their names."""
    attrs = set()

    def _scan_body(obody, nbody):
        if len(obody) != len(nbody):
            return False
        for o_s, n_s in zip(obody, nbody):
            if type(o_s) is not type(n_s):
                return False
            if ast.dump(o_s, include_attributes=False) == ast.dump(n_s, include_attributes=False):
                continue
            if isinstance(o_s, ast.Assign) and len(o_s.targets) == 1 and len(n_s.targets) == 1:
                ot, nt = o_s.targets[0], n_s.targets[0]
                if isinstance(ot, ast.Name) and isinstance(nt, ast.Name) and ot.id == nt.id and ot.id.isupper() and len(ot.id) >= 3:
                    attrs.add(ot.id)
                    continue
                return False
            if isinstance(o_s, ast.AnnAssign) and isinstance(o_s.target, ast.Name) and isinstance(n_s.target, ast.Name):
                if (
                    o_s.target.id == n_s.target.id
                    and o_s.target.id.isupper()
                    and len(o_s.target.id) >= 3
                    and ast.dump(o_s.annotation, include_attributes=False) == ast.dump(n_s.annotation, include_attributes=False)
                ):
                    attrs.add(o_s.target.id)
                    continue
                return False
            if isinstance(o_s, ast.ClassDef) and o_s.name == n_s.name:
                if not _scan_body(o_s.body, n_s.body):
                    return False
                continue
            return False
        return True

    for o_cls, n_cls in changed_class_pairs:
        if not _scan_body(o_cls.body, n_cls.body):
            return None
    return attrs if attrs else None


def _get_import_time_attrs():
    global _IMPORT_TIME_ATTRS_CACHE
    if _IMPORT_TIME_ATTRS_CACHE is not None:
        return _IMPORT_TIME_ATTRS_CACHE
    found = set()
    pat = re.compile(r"\b[A-Z][A-Z0-9_]{2,}\b")
    for p in (REPO_ROOT / "sqlglot").rglob("*.py"):
        src = p.read_text(encoding="utf-8", errors="ignore")
        if "def __new__" not in src and "def __init_subclass__" not in src:
            continue
        try:
            tree = ast.parse(src)
        except SyntaxError:
            continue
        lines = src.splitlines()
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name in ("__new__", "__init_subclass__"):
                seg = "\n".join(lines[node.lineno - 1 : node.end_lineno])
                found.update(pat.findall(seg))
    _IMPORT_TIME_ATTRS_CACHE = found
    return found


def _attr_defuse_narrow(attr_names, base_nums, tm_files, tm_funcs, tm_lines, idxs_to_nums):
    """Narrow non-import-time ALL_CAPS class attribute edits via static def-use + line coverage."""
    imp_attrs = _get_import_time_attrs()
    if any(a in imp_attrs for a in attr_names):
        return None

    ref_nums = set()
    direct_test_nums = set()
    for attr in attr_names:
        q1, q2 = f'"{attr}"', f"'{attr}'"
        for folder in ("sqlglot", "tests"):
            root = REPO_ROOT / folder
            if not root.exists():
                continue
            for p in root.rglob("*.py"):
                rel = p.relative_to(REPO_ROOT).as_posix()
                txt = p.read_text(encoding="utf-8", errors="ignore")
                if attr not in txt:
                    continue
                if q1 in txt or q2 in txt:
                    return None
                if folder == "tests":
                    if rel not in tm_files:
                        return None
                    direct_test_nums.update(idxs_to_nums(tm_files[rel]))
                    continue
                _, tree = _get_old_ast(rel)
                if q1 in txt or q2 in txt:
                    return None
                if tree is None:
                    return None

                if folder == "tests":
                    if rel not in tm_files:
                        return None
                    direct_test_nums.update(idxs_to_nums(tm_files[rel]))
                    continue

                # Collect class-body LHS definition target ids so we skip pure definitions
                def_target_ids = set()
                for n in ast.walk(tree):
                    if isinstance(n, ast.ClassDef):
                        for stmt in n.body:
                            if isinstance(stmt, ast.Assign):
                                for t in stmt.targets:
                                    if isinstance(t, ast.Name) and t.id == attr:
                                        def_target_ids.add(id(t))
                            elif isinstance(stmt, ast.AnnAssign):
                                if isinstance(stmt.target, ast.Name) and stmt.target.id == attr:
                                    def_target_ids.add(id(stmt.target))

                # Collect function/lambda spans to verify every reference is runtime (not import-time)
                func_spans = []
                for n in ast.walk(tree):
                    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
                        s = getattr(n, "lineno", None)
                        e = getattr(n, "end_lineno", s)
                        if s is not None:
                            func_spans.append((s, e, n.lineno))

                ref_lines = set()
                for n in ast.walk(tree):
                    is_ref = (isinstance(n, ast.Name) and n.id == attr and id(n) not in def_target_ids) or (
                        isinstance(n, ast.Attribute) and n.attr == attr
                    )
                    if not is_ref:
                        continue
                    ln = getattr(n, "lineno", None)
                    if ln is None:
                        return None
                    enc = [fs for fs in func_spans if fs[0] <= ln <= fs[1]]
                    if not enc:
                        return None  # module/class-level read -> import-time dependency!
                    ref_lines.add(ln)

                if ref_lines:
                    flm = tm_lines.get(rel, {})
                    for ln in ref_lines:
                        l_nums, l_ok = _stmt_lines_lookup(rel, tree, {ln}, flm, tm_funcs, idxs_to_nums)
                        if l_ok:
                            ref_nums.update(l_nums)
                        else:
                            # If enclosing function was traced and line wasn't hit -> 0 tests reached it; else fallback
                            enc_f = [fs[2] for fs in func_spans if fs[0] <= ln <= fs[1]]
                            if any(f"{rel}:{fln}" in tm_funcs for fln in enc_f):
                                continue
                            if rel not in tm_files:
                                return None

    narrowed = (base_nums & ref_nums) | direct_test_nums
    return narrowed if narrowed else None



ANNOTATION_SENSITIVE_FILES = {
    "sqlglot/_typing.py",
    "sqlglot/diff.py",
    "sqlglot/lineage.py",
    "sqlglot/optimizer/pushdown_projections.py",
}


def _has_future_annotations(tree):
    for node in tree.body[:6]:
        if isinstance(node, ast.ImportFrom) and node.module == "__future__":
            if any(a.name == "annotations" for a in node.names):
                return True
    return False


def _is_type_checking_test(test):
    if isinstance(test, ast.Name) and test.id == "TYPE_CHECKING":
        return True
    if isinstance(test, ast.Attribute) and test.attr == "TYPE_CHECKING":
        return True
    return False


class _RuntimeNormalizer(ast.NodeTransformer):
    def __init__(self, strip_docstrings=True, strip_annotations=False):
        self.strip_docstrings = strip_docstrings
        self.strip_annotations = strip_annotations

    def _strip_doc(self, body):
        if (
            self.strip_docstrings
            and body
            and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)
        ):
            return body[1:]
        return body

    def visit_Module(self, node):
        node.body = self._strip_doc(node.body)
        self.generic_visit(node)
        return node

    def visit_ClassDef(self, node):
        node.body = self._strip_doc(node.body)
        self.generic_visit(node)
        return node

    def visit_FunctionDef(self, node):
        node.body = self._strip_doc(node.body)
        if self.strip_annotations:
            node.returns = None
            for a in list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs):
                a.annotation = None
            if node.args.vararg:
                node.args.vararg.annotation = None
            if node.args.kwarg:
                node.args.kwarg.annotation = None
        self.generic_visit(node)
        return node

    def visit_AsyncFunctionDef(self, node):
        return self.visit_FunctionDef(node)

    def visit_AnnAssign(self, node):
        self.generic_visit(node)
        if self.strip_annotations:
            if node.value is None:
                return ast.Pass()
            return ast.Assign(targets=[node.target], value=node.value)
        return node

    def visit_If(self, node):
        if _is_type_checking_test(node.test):
            # TYPE_CHECKING is always False at runtime; keep only orelse
            if node.orelse:
                return [self.visit(s) for s in node.orelse]
            return ast.Pass()
        self.generic_visit(node)
        return node


def _is_runtime_noop_ast(rel_file, old_text, new_text):
    """True if old_text and new_text are identical after stripping docstrings, TYPE_CHECKING, and postponed annotations."""
    try:
        o_tree = ast.parse(old_text)
        n_tree = ast.parse(new_text)
    except SyntaxError:
        return False
    strip_doc = (rel_file != "sqlglot/expressions/core.py")
    strip_ann = (
        rel_file not in ANNOTATION_SENSITIVE_FILES
        and _has_future_annotations(o_tree)
        and _has_future_annotations(n_tree)
    )
    o_norm = _RuntimeNormalizer(strip_docstrings=strip_doc, strip_annotations=strip_ann).visit(o_tree)
    n_norm = _RuntimeNormalizer(strip_docstrings=strip_doc, strip_annotations=strip_ann).visit(n_tree)
    return ast.dump(o_norm, include_attributes=False) == ast.dump(n_norm, include_attributes=False)


def _extract_exp_key_name(key_node):
    if isinstance(key_node, ast.Attribute) and isinstance(key_node.value, ast.Name) and key_node.value.id in ("exp", "expressions"):
        return key_node.attr
    return None



STRING_DICT_NAMES = {
    "FUNCTIONS",
    "FUNCTIONS_WITH_ALIASED_ARGS",
    "SHOW_PARSERS",
    "STATEMENT_PARSERS",
    "PROPERTY_PARSERS",
    "KEYWORDS",
    "DATE_PART_MAPPING",
    "TYPE_MAPPING",
}


def _extract_str_key(key_node):
    if isinstance(key_node, ast.Constant) and isinstance(key_node.value, str):
        return key_node.value
    return None


def _changed_str_dict_keys(changed_class_pairs):
    """If class edits ONLY change values for existing string keys in known dicts, return list of (cls_name, dict_name, key_str)."""
    hits = []
    for o_cls, n_cls in changed_class_pairs:
        if len(o_cls.body) != len(n_cls.body):
            return None
        for o_s, n_s in zip(o_cls.body, n_cls.body):
            if type(o_s) is not type(n_s):
                return None
            if ast.dump(o_s, include_attributes=False) == ast.dump(n_s, include_attributes=False):
                continue
            dname, o_val, n_val = None, None, None
            if isinstance(o_s, ast.Assign) and len(o_s.targets) == 1 and len(n_s.targets) == 1:
                if isinstance(o_s.targets[0], ast.Name) and isinstance(n_s.targets[0], ast.Name) and o_s.targets[0].id == n_s.targets[0].id:
                    dname, o_val, n_val = o_s.targets[0].id, o_s.value, n_s.value
            elif isinstance(o_s, ast.AnnAssign) and isinstance(o_s.target, ast.Name) and isinstance(n_s.target, ast.Name):
                if o_s.target.id == n_s.target.id:
                    dname, o_val, n_val = o_s.target.id, o_s.value, n_s.value
            if dname not in STRING_DICT_NAMES or not isinstance(o_val, ast.Dict) or not isinstance(n_val, ast.Dict):
                return None

            o_map = {}
            for k, v in zip(o_val.keys, o_val.values):
                if k is None:
                    return None  # dict unpacking (**...) -> too risky to narrow by key
                sk = _extract_str_key(k)
                if sk is None:
                    return None
                o_map[sk] = ast.dump(v, include_attributes=False)

            n_map = {}
            for k, v in zip(n_val.keys, n_val.values):
                if k is None:
                    return None
                sk = _extract_str_key(k)
                if sk is None:
                    return None
                n_map[sk] = ast.dump(v, include_attributes=False)

            # Require exact same key set (no added/removed/renamed keys)
            if set(o_map.keys()) != set(n_map.keys()):
                return None

            for sk in o_map:
                if o_map[sk] != n_map[sk]:
                    hits.append((o_cls.name, dname, sk))

    return hits if hits else None


def _changed_exp_dict_keys(changed_class_pairs):
    """If class edits ONLY change values for existing exp.Foo keys in class-level dicts, return (dict_names, exp_names)."""
    dict_names = set()
    exp_names = set()
    for o_cls, n_cls in changed_class_pairs:
        if len(o_cls.body) != len(n_cls.body):
            return None
        for o_s, n_s in zip(o_cls.body, n_cls.body):
            if type(o_s) is not type(n_s):
                return None
            if ast.dump(o_s, include_attributes=False) == ast.dump(n_s, include_attributes=False):
                continue
            dname, o_val, n_val = None, None, None
            if isinstance(o_s, ast.Assign) and len(o_s.targets) == 1 and len(n_s.targets) == 1:
                if isinstance(o_s.targets[0], ast.Name) and isinstance(n_s.targets[0], ast.Name) and o_s.targets[0].id == n_s.targets[0].id:
                    dname, o_val, n_val = o_s.targets[0].id, o_s.value, n_s.value
            elif isinstance(o_s, ast.AnnAssign) and isinstance(o_s.target, ast.Name) and isinstance(n_s.target, ast.Name):
                if o_s.target.id == n_s.target.id:
                    dname, o_val, n_val = o_s.target.id, o_s.value, n_s.value
            if not isinstance(o_val, ast.Dict) or not isinstance(n_val, ast.Dict):
                return None
            # Compare dict entries by key dump
            o_map = {}
            for k, v in zip(o_val.keys, o_val.values):
                if k is None:
                    o_map[("__UNPACK__", ast.dump(v, include_attributes=False))] = (k, v)
                else:
                    o_map[ast.dump(k, include_attributes=False)] = (k, v)
            n_map = {}
            for k, v in zip(n_val.keys, n_val.values):
                if k is None:
                    n_map[("__UNPACK__", ast.dump(v, include_attributes=False))] = (k, v)
                else:
                    n_map[ast.dump(k, include_attributes=False)] = (k, v)
            all_ks = set(o_map.keys()) | set(n_map.keys())
            for kd in all_ks:
                ov = o_map.get(kd)
                nv = n_map.get(kd)
                if ov is not None and nv is not None:
                    if ast.dump(ov[1], include_attributes=False) == ast.dump(nv[1], include_attributes=False):
                        continue
                k_node = ov[0] if ov is not None else nv[0]
                ename = _extract_exp_key_name(k_node)
                if ename is None:
                    return None
                dict_names.add(dname)
                exp_names.add(ename)
    return (dict_names, exp_names) if exp_names else None


def _changed_test_methods(old_ast, new_ast):
    """If edits in a tests/*.py file are strictly inside existing test_* methods, return [(cls_name, method_name)]."""
    if len(old_ast.body) != len(new_ast.body):
        return None
    changed = []
    for o, n in zip(old_ast.body, new_ast.body):
        if type(o) is not type(n):
            return None
        if ast.dump(o, include_attributes=False) == ast.dump(n, include_attributes=False):
            continue
        if isinstance(o, ast.ClassDef) and o.name == n.name:
            if len(o.body) != len(n.body):
                return None
            for om, nm in zip(o.body, n.body):
                if type(om) is not type(nm):
                    return None
                if ast.dump(om, include_attributes=False) == ast.dump(nm, include_attributes=False):
                    continue
                if isinstance(om, (ast.FunctionDef, ast.AsyncFunctionDef)) and om.name == nm.name and om.name.startswith("test_"):
                    changed.append((o.name, om.name))
                else:
                    return None
        elif isinstance(o, (ast.FunctionDef, ast.AsyncFunctionDef)) and o.name == n.name and o.name.startswith("test_"):
            changed.append((None, o.name))
        else:
            return None
    return changed if changed else None


def _has_pep263_change(old_text, new_text):
    old_top = "\n".join(old_text.splitlines()[:2])
    new_top = "\n".join(new_text.splitlines()[:2])
    return bool(PEP263_RE.search(old_top) or PEP263_RE.search(new_top)) and (old_top != new_top)


def analyze_file_patch(rel_file, info):
    full = REPO_ROOT / rel_file
    if info["is_del"]:
        return False, False, None, set(), True, None, None
    if info["is_new"]:
        new_lines = [hl[1:] for _, _, _, _, hlines in info["hunks"] for hl in hlines if hl.startswith("+")]
        new_text = "\n".join(new_lines) + "\n"
        if rel_file.endswith(".py"):
            try:
                ast.parse(new_text)
            except SyntaxError:
                return False, True, new_text, set(), True, None, None
        return False, False, new_text, set(), True, None, None

    if not full.exists():
        return False, False, None, set(), True, None, None

    if not rel_file.endswith(".py"):
        old_text = full.read_text(encoding="utf-8", errors="ignore")
        new_text = apply_hunks(old_text, info["hunks"])
        return (old_text == new_text), False, new_text, set(), True, None, None

    old_text, old_ast = _get_old_ast(rel_file)
    if old_text is None:
        return False, False, None, set(), True, None, None
    new_text = apply_hunks(old_text, info["hunks"])

    if _has_pep263_change(old_text, new_text):
        try:
            ast.parse(new_text)
            return False, False, new_text, set(), True, old_ast, None
        except SyntaxError:
            return False, True, new_text, set(), True, old_ast, None

    if old_ast is None:
        return False, False, new_text, set(), True, None, None
    try:
        new_ast = ast.parse(new_text)
    except SyntaxError:
        return False, True, new_text, set(), True, old_ast, None

    if ast.dump(old_ast, include_attributes=False) == ast.dump(new_ast, include_attributes=False):
        return True, False, new_text, set(), False, old_ast, new_ast
    if _is_runtime_noop_ast(rel_file, old_text, new_text):
        return True, False, new_text, set(), False, old_ast, new_ast
    if _is_semantically_equivalent_ast(old_ast, new_ast):
        return True, False, new_text, set(), False, old_ast, new_ast

    changed_defs = set()
    outside = _diff_ast_body(old_ast.body, new_ast.body, changed_defs)
    return False, False, new_text, changed_defs, outside, old_ast, new_ast


def optimize_workers_with_cost(test_nums, dur_ms):
    if not test_nums:
        return [], 0
    sorted_nums = sorted(test_nums, key=lambda n: dur_ms[n], reverse=True)
    best_workers = []
    best_cost = float("inf")
    max_k = min(8, len(sorted_nums))
    for k in range(1, max_k + 1):
        workers = [[] for _ in range(k)]
        loads = [0] * k
        for n in sorted_nums:
            idx = loads.index(min(loads))
            workers[idx].append(n)
            loads[idx] += dur_ms[n]
        cost = max(loads) + 2000 * k
        if cost < best_cost:
            best_cost = cost
            best_workers = [w for w in workers if w]
    return best_workers, best_cost


def _make_sync_executors(use_pickle):
    def _call(fn, *args, **kwargs):
        if use_pickle:
            try:
                args = pickle.loads(pickle.dumps(args))
                kwargs = pickle.loads(pickle.dumps(kwargs))
            except Exception:
                pass
        res = fn(*args, **kwargs)
        if use_pickle:
            try:
                res = pickle.loads(pickle.dumps(res))
            except Exception:
                pass
        return res

    class _SyncProcessPoolExecutor:
        def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
            if initializer is not None:
                initializer(*initargs)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False

        def submit(self, fn, /, *args, **kwargs):
            fut = concurrent.futures.Future()
            try:
                fut.set_result(_call(fn, *args, **kwargs))
            except BaseException as e:
                fut.set_exception(e)
            return fut

        def map(self, fn, *iterables, timeout=None, chunksize=1):
            return [_call(fn, *vals) for vals in zip(*iterables)]

        def shutdown(self, wait=True, *, cancel_futures=False):
            pass

    class _SyncAsyncResult:
        def __init__(self, val):
            self._val = val

        def get(self, timeout=None):
            return self._val

        def wait(self, timeout=None):
            pass

        def ready(self):
            return True

        def successful(self):
            return True

    class _SyncMPPool:
        def __init__(self, processes=None, initializer=None, initargs=(), **kwargs):
            if initializer is not None:
                initializer(*initargs)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc_val, exc_tb):
            return False

        def apply(self, func, args=(), kwds=None):
            return _call(func, *args, **(kwds or {}))

        def apply_async(self, func, args=(), kwds=None, callback=None, error_callback=None):
            res = _call(func, *args, **(kwds or {}))
            if callback:
                callback(res)
            return _SyncAsyncResult(res)

        def map(self, func, iterable, chunksize=None):
            return [_call(func, x) for x in iterable]

        def imap(self, func, iterable, chunksize=1):
            for x in iterable:
                yield _call(func, x)

        def imap_unordered(self, func, iterable, chunksize=1):
            for x in iterable:
                yield _call(func, x)

        def starmap(self, func, iterable, chunksize=None):
            return [_call(func, *x) for x in iterable]

        def close(self):
            pass

        def join(self):
            pass

        def terminate(self):
            pass

    return _SyncProcessPoolExecutor, _SyncMPPool


class _InMemoryLoader(importlib.abc.Loader):
    def __init__(self, source, filepath, is_pkg, pkg_dir):
        self._source = source
        self._filepath = filepath
        self._is_pkg = is_pkg
        self._pkg_dir = pkg_dir

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        module.__file__ = self._filepath
        if self._is_pkg:
            module.__path__ = [self._pkg_dir]
        code = compile(self._source, self._filepath, "exec")
        exec(code, module.__dict__)


class _PatchMetaFinder(importlib.abc.MetaPathFinder):
    def __init__(self, mod_map):
        self._mod_map = mod_map

    def find_spec(self, fullname, path, target=None):
        entry = self._mod_map.get(fullname)
        if entry is None:
            return None
        source, filepath, is_pkg, pkg_dir = entry
        loader = _InMemoryLoader(source, filepath, is_pkg, pkg_dir)
        spec = importlib.machinery.ModuleSpec(fullname, loader, origin=filepath, is_package=is_pkg)
        if is_pkg:
            spec.submodule_search_locations = [pkg_dir]
        return spec


def _needs_pickle_roundtrip(patched_files):
    for rel in patched_files:
        if rel == "sqlglot/serde.py" or rel.startswith("sqlglot/expressions/"):
            return True
    return False


def _exec_live_child(patched_files, cand_nums, test_by_num, dur_ms):
    os.environ["HOME"] = "/tmp"
    os.chdir(str(REPO_ROOT))
    src_str = str(SRC_DIR)
    sys.path[:] = [p for p in sys.path if p != src_str]
    sys.path.insert(0, str(REPO_ROOT))

    SyncPPE, SyncMP = _make_sync_executors(_needs_pickle_roundtrip(patched_files))
    concurrent.futures.ProcessPoolExecutor = SyncPPE
    multiprocessing.Pool = SyncMP

    mod_map = {}
    fixture_map = {}
    for rel_file, new_text in patched_files.items():
        if new_text is None:
            continue
        abs_path = str((REPO_ROOT / rel_file).resolve())
        if rel_file.endswith(".py"):
            if rel_file.endswith("/__init__.py"):
                mod_name = rel_file[:-12].replace("/", ".")
                is_pkg = True
                pkg_dir = str((REPO_ROOT / rel_file).parent.resolve())
            else:
                mod_name = rel_file[:-3].replace("/", ".")
                is_pkg = False
                pkg_dir = ""
            mod_map[mod_name] = (new_text, abs_path, is_pkg, pkg_dir)
        else:
            fixture_map[abs_path] = new_text

    if mod_map:
        sys.meta_path.insert(0, _PatchMetaFinder(mod_map))

    if fixture_map:
        orig_open = builtins.open
        orig_io_open = io.open

        def _maybe_mem(file, mode="r"):
            try:
                if isinstance(file, (str, os.PathLike)) and "w" not in str(mode) and "a" not in str(mode):
                    ap = os.path.abspath(os.fspath(file))
                    if ap in fixture_map:
                        txt = fixture_map[ap]
                        if "b" in str(mode):
                            return io.BytesIO(txt.encode("utf-8"))
                        return io.StringIO(txt)
            except Exception:
                pass
            return None

        def hooked_open(file, mode="r", *args, **kwargs):
            mem = _maybe_mem(file, mode)
            return mem if mem is not None else orig_open(file, mode, *args, **kwargs)

        def hooked_io_open(file, mode="r", *args, **kwargs):
            mem = _maybe_mem(file, mode)
            return mem if mem is not None else orig_io_open(file, mode, *args, **kwargs)

        builtins.open = hooked_open
        io.open = hooked_io_open

    grouped = defaultdict(list)
    for n in sorted(cand_nums, key=lambda x: dur_ms[x]):
        tid = test_by_num[n]["id"]
        parts = tid.split("::")
        mod_name = parts[0][:-3].replace("/", ".")
        cls_name = parts[1] if len(parts) >= 3 else None
        method_name = parts[-1]
        grouped[(mod_name, cls_name)].append((n, method_name))

    def _on_alarm(signum, frame):
        raise TimeoutError("live test timed out")

    signal.signal(signal.SIGALRM, _on_alarm)
    failed = set()

    for (mod_name, cls_name), items in grouped.items():
        try:
            mod = importlib.import_module(mod_name)
        except BaseException:
            for n, _ in items:
                failed.add(n)
            continue

        if cls_name is None:
            for n, fn_name in items:
                timeout = max(3, int((dur_ms[n] / 1000.0) * 3 + 3))
                signal.alarm(timeout)
                try:
                    getattr(mod, fn_name)()
                except BaseException:
                    failed.add(n)
                finally:
                    signal.alarm(0)
            continue

        cls = getattr(mod, cls_name, None)
        if cls is None:
            for n, _ in items:
                failed.add(n)
            continue

        try:
            if hasattr(cls, "setUpClass"):
                cls.setUpClass()
        except BaseException:
            for n, _ in items:
                failed.add(n)
            continue

        for n, method_name in items:
            timeout = max(3, int((dur_ms[n] / 1000.0) * 3 + 3))
            signal.alarm(timeout)
            try:
                tc = cls(method_name)
                res = unittest.TestResult()
                tc.run(res)
                if not res.wasSuccessful():
                    failed.add(n)
            except BaseException:
                failed.add(n)
            finally:
                signal.alarm(0)

        try:
            if hasattr(cls, "tearDownClass"):
                cls.tearDownClass()
        except BaseException:
            pass

    return sorted(failed)


def run_live_tests(patched_files, cand_nums, test_by_num, dur_ms):
    if not hasattr(os, "fork") or not REPO_ROOT.exists():
        return None
    if any(v is None for v in patched_files.values()):
        return None

    read_fd, write_fd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(read_fd)
        try:
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, 1)
            os.dup2(devnull, 2)
            os.close(devnull)
            sys.stdout = io.StringIO()
            sys.stderr = io.StringIO()
        except Exception:
            pass

        try:
            failed = _exec_live_child(patched_files, cand_nums, test_by_num, dur_ms)
            payload = json.dumps({"ok": True, "failed": failed}).encode("utf-8")
        except BaseException:
            payload = json.dumps({"ok": False}).encode("utf-8")

        try:
            with os.fdopen(write_fd, "wb") as wf:
                wf.write(payload)
        except Exception:
            pass
        os._exit(0)
    else:
        os.close(write_fd)
        chunks = []
        with os.fdopen(read_fd, "rb") as rf:
            while True:
                chunk = rf.read(65536)
                if not chunk:
                    break
                chunks.append(chunk)
        os.waitpid(pid, 0)
        raw = b"".join(chunks)
        if not raw:
            return None
        try:
            data = json.loads(raw.decode("utf-8"))
            if data.get("ok"):
                return set(data["failed"])
        except Exception:
            pass
        return None


def _preload_heavy_third_party():
    if not hasattr(os, "fork"):
        return
    for mod in ("numpy", "pandas", "pandas.testing", "duckdb", "pytz", "unittest.mock", "decimal", "datetime"):
        try:
            importlib.import_module(mod)
        except Exception:
            pass


def _load_test_map():
    gz_path = SRC_DIR / "test_map.json.gz"
    if gz_path.exists():
        with gzip.open(gz_path, "rt", encoding="utf-8") as f:
            return json.load(f)
    with open(SRC_DIR / "test_map.json", "r", encoding="utf-8") as f:
        return json.load(f)


def main():
    os.environ.setdefault("HOME", "/tmp")
    data_dir = os.environ.get("DATA_DIR", "/data")
    if not os.path.exists(data_dir):
        data_dir = "./data"

    with open(os.path.join(data_dir, "tests.json"), "r", encoding="utf-8") as f:
        tests = [t for t in json.load(f).get("tests", []) if "number" in t]

    id_to_num = {t["id"]: t["number"] for t in tests}
    test_by_num = {t["number"]: t for t in tests}
    dur_ms = {t["number"]: round(t["seconds"] * 1000) for t in tests}
    all_nums = set(id_to_num.values())
    never_drop_nums = {
        t["number"] for t in tests
        if t["id"] in NEVER_DROP_LIVE_IDS or t["file"] in NEVER_DROP_LIVE_FILES
    }

    tm = _load_test_map()
    tm_tests = tm["tests"]
    tm_files = tm["files"]
    tm_funcs = tm["funcs"]
    tm_lines = tm.get("lines", {})
    tm_exprs = tm.get("exprs", {})
    tm_dict_keys = tm.get("dict_keys", {})
    tm_fixtures = tm["fixtures"]
    expr_by_name = defaultdict(set)
    for ek, eidxs in tm_exprs.items():
        ename = ek.rsplit(":", 1)[-1]
        expr_by_name[ename].update(eidxs)

    def idxs_to_nums(idxs):
        out = set()
        for i in idxs:
            tid = tm_tests[i]
            if tid in id_to_num:
                out.add(id_to_num[tid])
        return out

    patch_paths = sorted(glob.glob(os.path.join(data_dir, "commits", "*.patch")))
    live_budget_used_s = 0.0
    live_calls = 0
    preloaded = False

    for patch_path in patch_paths:
        commit_id = os.path.basename(patch_path).replace(".patch", "")
        pinfo = parse_patch(patch_path)

        candidates = set()
        fixture_cands = set()
        patched_files = {}
        any_syn_err = False
        non_noop_count = 0

        for cfile, finfo in pinfo.items():
            is_noop, syn_err, new_text, changed_defs, outside_def, old_ast, new_ast = analyze_file_patch(cfile, finfo)
            if is_noop:
                continue

            non_noop_count += 1
            patched_files[cfile] = new_text
            if syn_err:
                any_syn_err = True

            if cfile.startswith("tests/fixtures/"):
                fc = set()
                if cfile in tm_fixtures:
                    fc.update(idxs_to_nums(tm_fixtures[cfile]))
                else:
                    stem = Path(cfile).stem.lower()
                    base = stem.split("__")[0].rstrip("s")
                    parts_u = base.split("_")
                    matched = False
                    for k in range(len(parts_u), 0, -1):
                        pref = "_".join(parts_u[:k])
                        if len(pref) < 4:
                            break
                        for t in tests:
                            if pref in t["id"].lower():
                                fc.add(t["number"])
                                matched = True
                        if matched:
                            break
                    if not matched:
                        parts_p = cfile.split("/")
                        if len(parts_p) >= 3:
                            tgt = f"tests/test_{parts_p[2]}.py"
                            fc.update(t["number"] for t in tests if t["file"] == tgt)
                candidates.update(fc)
                fixture_cands.update(fc)
            elif cfile.endswith(".py") and cfile.startswith("sqlglot/"):
                if not syn_err and not finfo["is_new"] and not finfo["is_del"] and not outside_def and changed_defs:
                    # 1. Statement-level line coverage inside modified function/lambda bodies
                    l_nums, l_ok = (
                        _stmt_lines_lookup(cfile, old_ast, finfo["old_lines"], tm_lines.get(cfile), tm_funcs, idxs_to_nums)
                        if old_ast is not None else (set(), False)
                    )
                    if l_ok and l_nums:
                        candidates.update(l_nums)
                    else:
                        missing_from_map = False
                        for dln in changed_defs:
                            key = f"{cfile}:{dln}"
                            if key in tm_funcs:
                                candidates.update(idxs_to_nums(tm_funcs[key]))
                            else:
                                missing_from_map = True
                        if missing_from_map:
                            f_cands = idxs_to_nums(tm_files.get(cfile, []))
                            candidates.update(f_cands if f_cands else all_nums)
                elif not syn_err and not finfo["is_new"] and not finfo["is_del"] and old_ast is not None and new_ast is not None:
                    # 2. Class-body edits: Expression subclass or Dialect Tokenizer/Parser/Generator narrowing
                    changed_classes = _changed_top_classes(old_ast, new_ast)
                    narrowed = set()
                    if changed_classes and cfile.startswith("sqlglot/expressions/"):
                        keys = [f"{cfile}:{o_cls.name}" for o_cls, _ in changed_classes]
                        if all(k in tm_exprs for k in keys):
                            for k in keys:
                                narrowed.update(idxs_to_nums(tm_exprs[k]))
                    elif changed_classes and cfile.startswith("sqlglot/dialects/"):
                        comps = _dialect_component_only(changed_classes)
                        if comps:
                            comp_cands = set()
                            ok_comp = True
                            for comp_key in comps:
                                cmap = tm.get(comp_key, {})
                                if cfile in cmap and cmap[cfile]:
                                    comp_cands.update(idxs_to_nums(cmap[cfile]))
                                else:
                                    ok_comp = False
                            if ok_comp and comp_cands:
                                narrowed.update(comp_cands)

                    base_cands = narrowed if narrowed else idxs_to_nums(tm_files.get(cfile, []))
                    if changed_classes and base_cands and cfile.startswith(("sqlglot/dialects/", "sqlglot/parsers/", "sqlglot/generators/", "sqlglot/generator.py", "sqlglot/parser.py", "sqlglot/typing/")):
                        exp_dict_res = _changed_exp_dict_keys(changed_classes)
                        if exp_dict_res:
                            dnames, enames = exp_dict_res
                            if all(en in expr_by_name for en in enames):
                                expr_nums = set()
                                for en in enames:
                                    expr_nums.update(idxs_to_nums(expr_by_name[en]))
                                inter = base_cands & expr_nums
                                if "EXPRESSION_METADATA" in dnames:
                                    inter |= {t["number"] for t in tests if t["file"] == "tests/test_typing.py"}
                                if inter:
                                    base_cands = inter
                        else:
                            sdict_hits = _changed_str_dict_keys(changed_classes)
                            if sdict_hits and tm_dict_keys:
                                dk_nums = set()
                                all_ok = True
                                for cname, dname, sk in sdict_hits:
                                    # Check exact class and any nested Parser/Tokenizer/Generator class
                                    matched_key = False
                                    for prefix in (f"{cfile}:{cname}.{dname}:{sk}", f"{cfile}:Parser.{dname}:{sk}", f"{cfile}:Tokenizer.{dname}:{sk}", f"{cfile}:Generator.{dname}:{sk}"):
                                        if prefix in tm_dict_keys and tm_dict_keys[prefix]:
                                            dk_nums.update(idxs_to_nums(tm_dict_keys[prefix]))
                                            matched_key = True
                                    if not matched_key:
                                        # Also check suffixed keys like "sqlglot/parsers/foo.py:FooParser.FUNCTIONS:BAR"
                                        for dk, idxs in tm_dict_keys.items():
                                            if dk.startswith(f"{cfile}:") and dk.endswith(f".{dname}:{sk}") and idxs:
                                                dk_nums.update(idxs_to_nums(idxs))
                                                matched_key = True
                                                break
                                    if not matched_key:
                                        all_ok = False
                                        break
                                if all_ok and (base_cands & dk_nums):
                                    base_cands = base_cands & dk_nums
                            cattrs = _changed_all_caps_class_attrs(changed_classes)
                            if cattrs:
                                du = _attr_defuse_narrow(cattrs, base_cands, tm_files, tm_funcs, tm_lines, idxs_to_nums)
                                if du:
                                    base_cands = du
                    candidates.update(base_cands if base_cands else all_nums)
                else:
                    f_cands = idxs_to_nums(tm_files.get(cfile, []))
                    candidates.update(f_cands if f_cands else all_nums)
            elif cfile.startswith("tests/"):
                t_narrow = set()
                if not syn_err and not finfo["is_new"] and not finfo["is_del"] and old_ast is not None and new_ast is not None:
                    cmethods = _changed_test_methods(old_ast, new_ast)
                    if cmethods:
                        for cname, mname in cmethods:
                            tid = f"{cfile}::{cname}::{mname}" if cname else f"{cfile}::{mname}"
                            if tid in id_to_num:
                                t_narrow.add(id_to_num[tid])
                            else:
                                t_narrow.clear()
                                break
                if t_narrow:
                    candidates.update(t_narrow)
                elif cfile in tm_files:
                    candidates.update(idxs_to_nums(tm_files[cfile]))
                else:
                    candidates.update(t["number"] for t in tests if t["file"] == cfile)
            elif cfile in tm_files:
                candidates.update(idxs_to_nums(tm_files[cfile]))
            elif cfile in tm_fixtures:
                candidates.update(idxs_to_nums(tm_fixtures[cfile]))
            else:
                candidates.update(all_nums)

        if non_noop_count == 0 or not candidates:
            print(json.dumps({"commit": commit_id, "workers": []}), flush=True)
            continue

        final_nums = candidates
        if not any_syn_err and live_budget_used_s < TOTAL_LIVE_BUDGET_S:
            _, static_cost_ms = optimize_workers_with_cost(candidates, dur_ms)
            keep_blind = (
                {n for n in candidates if dur_ms[n] > LIVE_SINGLE_MAX_S * 1000}
                | fixture_cands
                | (candidates & never_drop_nums)
            )
            maybe_live = sorted((candidates - keep_blind), key=lambda n: dur_ms[n])

            if maybe_live:
                _, blind_cost_ms = optimize_workers_with_cost(keep_blind, dur_ms)
                live_sum_s = sum(dur_ms[n] for n in maybe_live) / 1000.0
                expected_savings_s = (static_cost_ms - blind_cost_ms) / 1000.0 - (0.45 * (2.0 + 0.50 * live_sum_s) if not keep_blind else 0.45 * 0.50 * live_sum_s)
                est_cpu_s = LIVE_FIXED_OVERHEAD_S + LIVE_SPEED_FACTOR * live_sum_s

                if (
                    live_sum_s <= LIVE_COMMIT_MAX_S
                    and est_cpu_s < LIVE_EV_THRESHOLD * expected_savings_s
                    and live_budget_used_s + est_cpu_s <= TOTAL_LIVE_BUDGET_S
                ):
                    if not preloaded and any(
                        test_by_num[n]["file"] in ("tests/test_executor.py", "tests/dialects/test_duckdb.py")
                        or "dataframe" in test_by_num[n]["file"]
                        for n in maybe_live
                    ):
                        _preload_heavy_third_party()
                        preloaded = True
                    live_calls += 1
                    t0 = time.perf_counter()
                    failed_live = run_live_tests(patched_files, maybe_live, test_by_num, dur_ms)
                    dt = time.perf_counter() - t0
                    live_budget_used_s += dt
                    print(
                        f"[live] {commit_id}: {len(maybe_live)}->{len(failed_live) if failed_live is not None else 'NONE'} ({dt:.2f}s)",
                        file=sys.stderr,
                        flush=True,
                    )
                    if failed_live is not None:
                        final_nums = keep_blind | failed_live

        workers, _ = optimize_workers_with_cost(final_nums, dur_ms)
        print(json.dumps({"commit": commit_id, "workers": workers}), flush=True)

    if resource is not None:
        r_self = resource.getrusage(resource.RUSAGE_SELF)
        r_child = resource.getrusage(resource.RUSAGE_CHILDREN)
        cpu_s = (r_self.ru_utime + r_self.ru_stime) + (r_child.ru_utime + r_child.ru_stime)
        print(f"[stats] live_calls={live_calls} cpu={cpu_s:.3f}s", file=sys.stderr, flush=True)


if __name__ == "__main__":
    main()