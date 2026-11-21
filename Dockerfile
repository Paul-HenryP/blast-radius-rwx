FROM python:3.12-slim
WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt duckdb pytz numpy pandas python-dateutil tzdata setuptools

RUN apt-get update && apt-get install -y git && rm -rf /var/lib/apt/lists/*
RUN git clone https://github.com/tobymao/sqlglot.git && cd sqlglot && git checkout eb11aec4be8cb2122afe713a4816662c3f0fb2fa

COPY src/ ./src/

WORKDIR /app
ENTRYPOINT ["python", "/app/src/main.py"]