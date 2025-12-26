import os, json, glob
import psycopg2

DSN = os.environ["DATABASE_URL"]
DATA_DIR = "data"  # adapte si ton dossier s'appelle autrement

def main():
    files = glob.glob(os.path.join(DATA_DIR, "*.json"))
    if not files:
        print(f"Aucun .json trouvé dans {DATA_DIR}/")
        return

    with psycopg2.connect(DSN) as conn:
        with conn.cursor() as cur:
            cur.execute("""
                CREATE TABLE IF NOT EXISTS public.kv_store (
                    k TEXT PRIMARY KEY,
                    v JSONB NOT NULL,
                    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                );
            """)
            for path in files:
                key = os.path.basename(path)
                with open(path, "r", encoding="utf-8") as f:
                    payload = json.load(f)

                cur.execute("""
                    INSERT INTO public.kv_store (k, v, updated_at)
                    VALUES (%s, %s::jsonb, NOW())
                    ON CONFLICT (k) DO UPDATE
                    SET v = EXCLUDED.v, updated_at = NOW();
                """, (key, json.dumps(payload, ensure_ascii=False)))

    print(f"OK: {len(files)} fichiers synchronisés vers kv_store.")

if __name__ == "__main__":
    main()
