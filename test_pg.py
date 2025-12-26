@'
import os
import psycopg2

dsn = os.environ["DATABASE_URL"]

with psycopg2.connect(dsn) as conn:
    with conn.cursor() as cur:
        cur.execute("select current_database(), current_user, inet_server_port();")
        print(cur.fetchone())
'@ | Set-Content -Encoding UTF8 .\test_pg.py
