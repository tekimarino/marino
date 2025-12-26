from __future__ import annotations

import os
import json
import uuid
import secrets
import shutil
import zipfile
import unicodedata
import math
from pathlib import Path
from datetime import datetime, timezone, timedelta, date
from functools import wraps
from typing import Any, Dict, List, Optional, Tuple

import io

# Optional PostgreSQL backend (JSON stored as JSONB in a key/value table)
try:
    import psycopg2
    from psycopg2 import pool as pg_pool
    from psycopg2.extras import Json as PgJson
except Exception:  # pragma: no cover
    psycopg2 = None
    pg_pool = None
    PgJson = None

from flask import (
    Flask,
    render_template,
    request,
    redirect,
    url_for,
    session,
    flash,
    abort,
    send_file,
    jsonify,
)
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename


# ----------------------------
# Pagination helper
# ----------------------------

def _paginate(items: List[Any], page: int, per_page: int) -> Dict[str, Any]:
    """Return a slice + metadata. Page is 1-indexed."""
    if per_page <= 0:
        per_page = 10
    try:
        page = int(page)
    except Exception:
        page = 1
    if page < 1:
        page = 1

    total = len(items)
    total_pages = max(1, (total + per_page - 1) // per_page)
    if page > total_pages:
        page = total_pages

    start = (page - 1) * per_page
    end = start + per_page
    return {
        "items": items[start:end],
        "page": page,
        "per_page": per_page,
        "total": total,
        "total_pages": total_pages,
        "pages": total_pages,
        "has_prev": page > 1,
        "has_next": page < total_pages,
        "prev_page": page - 1,
        "next_page": page + 1,
    }


# ----------------------------
# Configuration
# ----------------------------
APP_NAME = "Recensement Électoral 2028"
APP_VERSION = "10.15"  # cache-busting CSS + UI version

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
UPLOADS_DIR = os.path.join(BASE_DIR, "uploads")
BACKUPS_DIR = os.path.join(BASE_DIR, "backups")

USERS_FILE = os.path.join(DATA_DIR, "users.json")
ZONES_FILE = os.path.join(DATA_DIR, "zones.json")
REG_FILE = os.path.join(DATA_DIR, "registrations.json")

CENTERS_FILE = os.path.join(DATA_DIR, "centers.json")
OBJECTIVES_FILE = os.path.join(DATA_DIR, "objectives.json")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")
APPROVALS_QUEUE_FILE = os.path.join(DATA_DIR, "approvals_queue.json")
# Alias rétro-compatibilité (anciens patches)
APPROVAL_QUEUE_FILE = APPROVALS_QUEUE_FILE
AUDIT_FILE = os.path.join(DATA_DIR, "audit_log.json")

PAYROLL_FILE = os.path.join(DATA_DIR, "payroll.json")
PAY_RATE_CFA = 500
PAY_FIXED_BONUS_CFA = 10000


def _pay_rate_cfa() -> int:
    """Read pay rate from settings (fallback to default constant)."""
    s = _get_settings()
    try:
        v = int(s.get("pay_rate", PAY_RATE_CFA))
        return v if v >= 0 else PAY_RATE_CFA
    except Exception:
        return PAY_RATE_CFA



def _pay_fixed_bonus_cfa() -> int:
    """Read fixed bonus from settings (fallback to default constant)."""
    s = _get_settings()
    try:
        v = int(s.get("pay_fixed_bonus", PAY_FIXED_BONUS_CFA))
        return v if v >= 0 else 0
    except Exception:
        return PAY_FIXED_BONUS_CFA


def _pay_period_days() -> int:
    """Read pay period (in days) from settings (fallback to default constant)."""
    s = _get_settings()
    try:
        v = int(s.get("pay_period_days", PAY_PERIOD_DAYS))
        return v if v > 0 else PAY_PERIOD_DAYS
    except Exception:
        return PAY_PERIOD_DAYS
PAY_PERIOD_DAYS = 14

SMS_CONFIG_FILE = os.path.join(DATA_DIR, "sms_config.json")
SMS_CAMPAIGNS_FILE = os.path.join(DATA_DIR, "sms_campaigns.json")
SMS_OUTBOX_FILE = os.path.join(DATA_DIR, "sms_outbox.json")
SMS_LOGS_FILE = os.path.join(DATA_DIR, "sms_logs.json")

DEFAULT_SECRET = "CHANGE-ME-SECRET-KEY-2028"
SECRET_KEY = os.environ.get("SECRET_KEY", DEFAULT_SECRET)

ALLOWED_UPLOAD_EXT = {".jpg", ".jpeg", ".png", ".pdf"}
MAX_UPLOAD_MB = 5

MAX_SMS_SEND_PER_REQUEST = 200  # sécurité: évite de bloquer le serveur

# Statuts dossiers
STATUS_DRAFT = "DRAFT"
STATUS_PENDING = "PENDING"
STATUS_NEEDS_CORRECTION = "NEEDS_CORRECTION"
STATUS_VERIFIED = "VERIFIED"  # validé par superviseur
STATUS_APPROVED = "APPROVED"  # approuvé par admin (si double validation)
STATUS_REJECTED = "REJECTED"


STATUS_PAID = "PAID"  # utilisé par le module de paie / historique
STATUS_PENDING_REVIEW = "PENDING_REVIEW"  # alias legacy
app = Flask(__name__)
app.secret_key = SECRET_KEY


# ----------------------------
# Jinja filters
# ----------------------------

@app.template_filter("format_cfa")
def _jinja_format_cfa(value):
    """Format int as '150 000 F CFA'."""
    try:
        x = int(round(float(value)))
    except Exception:
        x = 0
    return f"{x:,}".replace(",", " " ) + " F CFA"



@app.template_filter("format_int")
def _jinja_format_int(value):
    """Format int as '150 000'."""
    try:
        x = int(round(float(value)))
    except Exception:
        return ""
    return f"{x:,}".replace(",", " ")


@app.template_filter("prettyjson")
def _jinja_prettyjson(value):
    try:
        return json.dumps(value, ensure_ascii=False, indent=2)
    except Exception:
        return str(value)



# ----------------------------
# Storage helpers
# - Default: JSON files in data/
# - Optional: PostgreSQL (JSONB) when DATABASE_URL is set
# ----------------------------


# --- PostgreSQL KV-store (optional) ---
_PG_POOL = None

def _db_url() -> Optional[str]:
    # DigitalOcean & many platforms use DATABASE_URL
    return (
        os.environ.get("DATABASE_URL")
        or os.environ.get("POSTGRES_URL")
        or os.environ.get("POSTGRESQL_URL")
        or os.environ.get("POSTGRES_CONNECTION_STRING")
    )

def _db_enabled() -> bool:
    return bool(_db_url()) and psycopg2 is not None and pg_pool is not None and PgJson is not None

def _db_pool() -> "pg_pool.SimpleConnectionPool":
    global _PG_POOL
    if _PG_POOL is None:
        url = _db_url()
        if not url:
            raise RuntimeError("DATABASE_URL manquant.")
        _PG_POOL = pg_pool.SimpleConnectionPool(minconn=1, maxconn=5, dsn=url)
        conn = _PG_POOL.getconn()
        try:
            conn.autocommit = True
            with conn.cursor() as cur:
                cur.execute(
                    """
                    CREATE TABLE IF NOT EXISTS kv_store (
                        k TEXT PRIMARY KEY,
                        v JSONB NOT NULL,
                        updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                    );
                    """
                )
        finally:
            _PG_POOL.putconn(conn)
    return _PG_POOL

def _kv_get(key: str) -> Any:
    pool = _db_pool()
    conn = pool.getconn()
    try:
        with conn.cursor() as cur:
            cur.execute("SELECT v FROM kv_store WHERE k=%s", (key,))
            row = cur.fetchone()
            if not row:
                return None
            val = row[0]
            if isinstance(val, str):
                try:
                    return json.loads(val)
                except Exception:
                    return None
            return val
    finally:
        pool.putconn(conn)

def _kv_set(key: str, data: Any) -> None:
    pool = _db_pool()
    conn = pool.getconn()
    try:
        conn.autocommit = True
        with conn.cursor() as cur:
            cur.execute(
                """
                INSERT INTO kv_store (k, v, updated_at)
                VALUES (%s, %s, NOW())
                ON CONFLICT (k) DO UPDATE SET v=EXCLUDED.v, updated_at=NOW();
                """,
                (key, PgJson(data, dumps=lambda x: json.dumps(x, ensure_ascii=False))),
            )
    finally:
        pool.putconn(conn)

def _kv_dump_all() -> Dict[str, Any]:
    pool = _db_pool()
    conn = pool.getconn()
    try:
        with conn.cursor() as cur:
            cur.execute("SELECT k, v FROM kv_store ORDER BY k ASC")
            rows = cur.fetchall() or []
        out: Dict[str, Any] = {}
        for k, v in rows:
            if isinstance(v, str):
                try:
                    out[k] = json.loads(v)
                except Exception:
                    out[k] = v
            else:
                out[k] = v
        return out
    finally:
        pool.putconn(conn)


def _load_json(path: str, default: Any) -> Any:
    """Load JSON from file or (if enabled) from PostgreSQL kv_store.

    If PostgreSQL is enabled and the key doesn't exist yet, we auto-seed it
    from the local file (if present) or from the provided default.
    """
    if _db_enabled():
        key = os.path.basename(path)
        val = _kv_get(key)
        if val is not None:
            return val

        seed = default
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    seed = json.load(f)
            except Exception:
                seed = default

        try:
            _kv_set(key, seed)
        except Exception:
            pass
        return seed

    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return default
    except json.JSONDecodeError:
        return default

def _atomic_write(path: str, content: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(content)
    os.replace(tmp, path)


def _save_json(path: str, data: Any) -> None:
    """Save JSON to file and (optionally) to PostgreSQL kv_store.

    When DATABASE_URL is set, PostgreSQL becomes the source of truth.
    By default we still write JSON files on disk (handy for backups/debugging).
    Set DB_ONLY=1 to disable writing JSON files on disk.
    """
    if _db_enabled():
        key = os.path.basename(path)
        try:
            _kv_set(key, data)
        except Exception:
            pass

        if (os.environ.get("DB_ONLY") or "").strip().lower() in ("1", "true", "yes", "y"):
            return

    _atomic_write(path, json.dumps(data, ensure_ascii=False, indent=2))

def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _norm_bool(value: Any, default: bool = False) -> bool:
    """Normalize a value (from form/json) into a strict boolean."""
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    s = str(value).strip().lower()
    if s in ("1", "true", "yes", "y", "on", "oui", "vrai"):
        return True
    if s in ("0", "false", "no", "n", "off", "non", "faux"):
        return False
    return default


def _ensure_data_files() -> None:
    """Create missing files ONLY. Never overwrite existing data."""
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(UPLOADS_DIR, exist_ok=True)
    os.makedirs(BACKUPS_DIR, exist_ok=True)

    if not os.path.exists(ZONES_FILE):
        zones = [
            {"id": str(uuid.uuid4()), "name": "Adiaho", "active": True},
            {"id": str(uuid.uuid4()), "name": "Kodjoboue", "active": True},
            {"id": str(uuid.uuid4()), "name": "Résidentiel", "active": True},
            {"id": str(uuid.uuid4()), "name": "Samo est", "active": True},
            {"id": str(uuid.uuid4()), "name": "Samo ouest", "active": True},
            {"id": str(uuid.uuid4()), "name": "Begneri", "active": True},
            {"id": str(uuid.uuid4()), "name": "Koumassi", "active": True},
            {"id": str(uuid.uuid4()), "name": "Bronoukro", "active": True},
            {"id": str(uuid.uuid4()), "name": "Yaou ancien quartier", "active": True},
            {"id": str(uuid.uuid4()), "name": "Yaou nouveau quarier", "active": True},
            {"id": str(uuid.uuid4()), "name": "Yaou Ekressinville", "active": True},
        ]
        _save_json(ZONES_FILE, zones)

    if not os.path.exists(USERS_FILE):
        zones = _load_json(ZONES_FILE, [])
        zone_id = zones[0]["id"] if zones else None
        users = [
            {
                "id": str(uuid.uuid4()),
                "username": "admin",
                "full_name": "Administrateur",
                "role": "admin",
                "zone_id": None,
                "supervisor_id": None,
                "password_hash": generate_password_hash("Admin2028@"),
                "created_at": _now_iso(),
                "is_active": True,
            },
            {
                "id": str(uuid.uuid4()),
                "username": "sup_adiaho",
                "full_name": "Superviseur Adiaho",
                "role": "supervisor",
                "zone_id": zone_id,
                "supervisor_id": None,
                "password_hash": generate_password_hash("Sup2028@"),
                "created_at": _now_iso(),
                "is_active": True,
            },
        ]
        sup_id = users[1]["id"]
        users.append(
            {
                "id": str(uuid.uuid4()),
                "username": "agent_01",
                "full_name": "Agent Recenseur 01",
                "role": "agent",
                "zone_id": zone_id,
                "supervisor_id": sup_id,
                "password_hash": generate_password_hash("Agent2028@"),
                "created_at": _now_iso(),
                "is_active": True,
            }
        )
        _save_json(USERS_FILE, users)

    if not os.path.exists(REG_FILE):
        _save_json(REG_FILE, [])

    if not os.path.exists(CENTERS_FILE):
        # { zone_id: [ {"id":..., "name":..., "bureaux": ["BV01", ...]} ] }
        _save_json(CENTERS_FILE, {})

    if not os.path.exists(OBJECTIVES_FILE):
        # { zone_id: {"target": 0} }
        _save_json(OBJECTIVES_FILE, {})

    if not os.path.exists(SETTINGS_FILE):
        _save_json(SETTINGS_FILE, {"double_approval": True})

    if not os.path.exists(AUDIT_FILE):
        _save_json(AUDIT_FILE, [])

    if not os.path.exists(PAYROLL_FILE):
        _save_json(PAYROLL_FILE, [])

    if not os.path.exists(SMS_CONFIG_FILE):
        _save_json(
            SMS_CONFIG_FILE,
            {
                "mode": "dry_run",
                "sender_id": "Elections2028",
                "http_json": {
                    "url": "",
                    "token": "",
                    "to_field": "to",
                    "message_field": "message",
                    "sender_field": "sender",
                },
            },
        )

    if not os.path.exists(SMS_CAMPAIGNS_FILE):
        _save_json(SMS_CAMPAIGNS_FILE, [])

    if not os.path.exists(SMS_OUTBOX_FILE):
        _save_json(SMS_OUTBOX_FILE, [])

    if not os.path.exists(SMS_LOGS_FILE):
        _save_json(SMS_LOGS_FILE, [])


    # Approvals queue file (ids waiting for admin final approval)
    if not os.path.exists(APPROVALS_QUEUE_FILE):
        _save_json(APPROVALS_QUEUE_FILE, [])

# ----------------------------
# Domain helpers
# ----------------------------

def _get_settings() -> Dict[str, Any]:
    s = _load_json(SETTINGS_FILE, {})
    if not isinstance(s, dict):
        s = {}

    changed = False

    # Backward-compat: some older builds used "double_validation".
    if "double_approval" not in s and "double_validation" in s:
        s["double_approval"] = _norm_bool(s.get("double_validation"))
        changed = True

    # Defaults (never overwrite existing values)
    if "double_approval" not in s:
        s["double_approval"] = True
        changed = True
    s.setdefault("pay_rate", PAY_RATE_CFA)
    s.setdefault("pay_period_days", PAY_PERIOD_DAYS)

    # Normalize double_approval to a real boolean (handles strings like "false")
    s["double_approval"] = _norm_bool(s.get("double_approval"))

    # Normalize types
    try:
        s["pay_rate"] = int(s.get("pay_rate", PAY_RATE_CFA) or PAY_RATE_CFA)
    except Exception:
        s["pay_rate"] = PAY_RATE_CFA
    try:
        s["pay_period_days"] = int(s.get("pay_period_days", PAY_PERIOD_DAYS) or PAY_PERIOD_DAYS)
    except Exception:
        s["pay_period_days"] = PAY_PERIOD_DAYS

    if changed:
        _save_settings(s)

    return s


def _get_approval_queue() -> List[str]:
    q = _load_json(APPROVALS_QUEUE_FILE, [])
    if not isinstance(q, list):
        return []
    out: List[str] = []
    seen = set()
    for x in q:
        if x is None:
            continue
        sid = str(x).strip()
        if not sid or sid in seen:
            continue
        seen.add(sid)
        out.append(sid)
    return out


def _save_approval_queue(q: List[str]) -> None:
    # Keep it simple and atomic
    _save_json(APPROVALS_QUEUE_FILE, q)


def _queue_for_admin(reg_id: str) -> None:
    reg_id = str(reg_id).strip()
    if not reg_id:
        return
    q = _get_approval_queue()
    if reg_id not in q:
        q.append(reg_id)
        _save_approval_queue(q)


def _dequeue_for_admin(reg_id: str) -> None:
    reg_id = str(reg_id).strip()
    if not reg_id:
        return
    q = _get_approval_queue()
    if reg_id in q:
        q = [x for x in q if x != reg_id]
        _save_approval_queue(q)


def _save_settings(s: Dict[str, Any]) -> None:
    _save_json(SETTINGS_FILE, s)


def _get_centers_map() -> Dict[str, Any]:
    m = _load_json(CENTERS_FILE, {})
    return m if isinstance(m, dict) else {}


def _save_centers_map(m: Dict[str, Any]) -> None:
    _save_json(CENTERS_FILE, m)


def _get_objectives_map() -> Dict[str, Any]:
    m = _load_json(OBJECTIVES_FILE, {})
    return m if isinstance(m, dict) else {}


def _save_objectives_map(m: Dict[str, Any]) -> None:
    _save_json(OBJECTIVES_FILE, m)


def _audit(action: str, actor_id: str, target_type: str, target_id: str, details: Optional[Dict[str, Any]] = None) -> None:
    try:
        log = _load_json(AUDIT_FILE, [])
        if not isinstance(log, list):
            log = []
        safe_details: Dict[str, Any] = details or {}
        # Garantit que l'audit est toujours sérialisable (ex: datetime, set, etc.)
        try:
            json.dumps(safe_details)
        except Exception:
            try:
                safe_details = json.loads(json.dumps(safe_details, default=str))
            except Exception:
                safe_details = {"note": "details_non_serialisables"}

        log.append(
            {
                "id": str(uuid.uuid4()),
                "at": _now_iso(),
                "action": action,
                "actor_id": actor_id,
                "target_type": target_type,
                "target_id": target_id,
                "details": safe_details,
            }
        )
        # keep audit file reasonable
        if len(log) > 20000:
            log = log[-20000:]
        _save_json(AUDIT_FILE, log)
    except Exception:
        # audit must never crash the app
        pass


def _get_audit() -> List[Dict[str, Any]]:
    """Load audit events from disk safely.

    This helper is used by per-dossier history pages. It must never raise.
    """
    try:
        log = _load_json(AUDIT_FILE, [])
        if not isinstance(log, list):
            return []
        # Keep only dict entries (defensive against corrupted files)
        return [e for e in log if isinstance(e, dict)]
    except Exception:
        return []

def _inject_admin_decision_events(reg: Dict[str, Any], logs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Garantit que la décision admin (approbation / rejet) apparaît dans l'historique,
    même si des dossiers ont été approuvés avant la mise en place de l'audit.
    """
    try:
        actions = {e.get("action") for e in logs if isinstance(e, dict)}
        # Approval
        if _canon_status(reg.get("status")) == STATUS_APPROVED:
            at = reg.get("approved_at") or reg.get("admin_approved_at")
            actor = reg.get("approved_by") or reg.get("admin_approved_by") or ""
            if at and "reg.admin_approve" not in actions:
                logs.append(
                    {
                        "id": "synthetic-" + str(uuid.uuid4()),
                        "at": at,
                        "action": "reg.admin_approve",
                        "actor_id": str(actor),
                        "target_type": "registration",
                        "target_id": str(reg.get("id") or ""),
                        "details": {"changes": [{"field": "status", "from": "VERIFIED", "to": "APPROVED"}], "synthetic": True},
                    }
                )
        # Rejection
        if _canon_status(reg.get("status")) == STATUS_REJECTED:
            at = reg.get("rejected_at") or reg.get("admin_rejected_at")
            actor = reg.get("rejected_by") or reg.get("admin_rejected_by") or ""
            if at and "reg.admin_reject" not in actions:
                logs.append(
                    {
                        "id": "synthetic-" + str(uuid.uuid4()),
                        "at": at,
                        "action": "reg.admin_reject",
                        "actor_id": str(actor),
                        "target_type": "registration",
                        "target_id": str(reg.get("id") or ""),
                        "details": {"changes": [{"field": "status", "from": "VERIFIED", "to": "REJECTED"}], "synthetic": True},
                    }
                )
    except Exception:
        pass
    return logs



# ----------------------------
# Auth + users
# ----------------------------

def _get_users() -> List[Dict[str, Any]]:
    data = _load_json(USERS_FILE, [])
    return data if isinstance(data, list) else []


def _save_users(users: List[Dict[str, Any]]) -> None:
    _save_json(USERS_FILE, users)


def _find_user(user_id: str) -> Optional[Dict[str, Any]]:
    for u in _get_users():
        if u.get("id") == user_id:
            return u
    return None


def _get_zones() -> List[Dict[str, Any]]:
    data = _load_json(ZONES_FILE, [])
    return data if isinstance(data, list) else []


def _get_active_zones() -> List[Dict[str, Any]]:
    """Return only zones that are active (used in dropdowns and operational pages)."""
    return [z for z in _get_zones() if z.get("active", True)]


def _save_zones(zones: List[Dict[str, Any]]) -> None:
    _save_json(ZONES_FILE, zones)


def _zone_name(zone_id: Optional[str]) -> str:
    if not zone_id:
        return "-"
    for z in _get_zones():
        if z.get("id") == zone_id:
            return z.get("name") or "-"
    return "Zone inconnue"


# ----------------------------
# Registrations
# ----------------------------

def _canon_status(value: Any) -> str:
    """Normalize historical / user-provided status values to canonical internal constants.

    This makes the app resilient to older French labels (e.g., "Vérifié") or
    accidental casing/spaces.
    """

    if value is None:
        return STATUS_PENDING

    s = str(value).strip()
    if not s:
        return STATUS_PENDING

    # Upper + remove accents for robust matching (Vérifié -> VERIFIE)
    s_norm = unicodedata.normalize("NFKD", s)
    s_norm = "".join(ch for ch in s_norm if not unicodedata.combining(ch))
    u = s_norm.strip().upper()

    # Common synonyms / legacy values
    if u in {"DRAFT", "BROUILLON"}:
        return STATUS_DRAFT
    if u in {"PENDING", "EN ATTENTE", "EN_ATTENTE", "A TRAITER", "A_TRAITER"}:
        return STATUS_PENDING
    if u in {"NEEDS_CORRECTION", "A CORRIGER", "A_CORRIGER", "CORRECTION"}:
        return STATUS_NEEDS_CORRECTION
    if u in {"REJECTED", "REJETE", "REJETE", "REFUSE", "REFUSE"}:
        return STATUS_REJECTED
    # "VALIDATED/VALIDE" are legacy labels often used for supervisor verification.
    if u in {"VERIFIED", "VERIFIE", "VALIDATED", "VALIDE"}:
        return STATUS_VERIFIED
    if u in {"APPROVED", "APPROUVE"}:
        return STATUS_APPROVED
    if u in {"PAID", "PAYE", "PAYE"}:
        return STATUS_PAID

    # Unknown: keep normalized version (without leading/trailing spaces)
    return u


def _needs_admin_approval_flag(r: Dict[str, Any]) -> bool:
    """Retourne True si un dossier est marqué comme nécessitant l'approbation admin.

    On supporte plusieurs clés (historique/patched versions) pour éviter que
    l'écran "Approbations" reste vide après une validation superviseur.
    """
    if not isinstance(r, dict):
        return False

    keys = [
        "needs_admin_approval",
        "need_admin_approval",
        "needs_admin_approvals",
        "awaiting_admin_approval",
        "awaiting_admin",
        "admin_pending_approval",
        "pending_admin_approval",
        "requires_admin_approval",
        "approval_pending",
    ]
    return any(_norm_bool(r.get(k)) for k in keys)

def _normalize_reg(r: Dict[str, Any]) -> Tuple[Dict[str, Any], bool]:
    changed = False
    def _setdefault(k: str, v: Any) -> None:
        nonlocal changed
        if k not in r:
            r[k] = v
            changed = True

    _setdefault("telephone", "")
    _setdefault("polling_center", "")
    _setdefault("polling_station", "")
    _setdefault("status", STATUS_PENDING)
    # Canonicalize status to avoid missing items in lists (approvals, etc.)
    canon = _canon_status(r.get("status"))
    if r.get("status") != canon:
        r["status"] = canon
        changed = True
    _setdefault("notes", "")
    _setdefault("qc_notes", "")
    _setdefault("correction_reason", "")
    # Double-validation fields (safe defaults for older data)
    _setdefault("verified_by", "")
    _setdefault("verified_at", "")
    _setdefault("supervisor_verified", False)
    _setdefault("supervisor_verified_by", "")
    _setdefault("supervisor_verified_at", "")
    _setdefault("supervisor_status", "")
    _setdefault("supervisor_review", "")
    # Drapeau canonique (et compat) "en attente d'approbation admin"
    _setdefault("needs_admin_approval", False)
    # Récupère le drapeau si une ancienne clé existe
    na = _needs_admin_approval_flag(r)
    if r.get("needs_admin_approval") != na:
        r["needs_admin_approval"] = na
        changed = True
    _setdefault("admin_approved_by", "")
    _setdefault("admin_approved_at", "")
    # Normalise admin_approved en bool
    aa = _norm_bool(r.get("admin_approved"))
    if r.get("admin_approved") != aa:
        r["admin_approved"] = aa
        changed = True
    _setdefault("approved_by", "")
    _setdefault("approved_at", "")
    _setdefault("updated_by", "")
    _setdefault("updated_at", "")
    _setdefault("photos", [])
    _setdefault("sms_last_at", "")

    # Score de fiabilité (calculé automatiquement)
    _setdefault("reliability_score", 0)
    _setdefault("reliability_missing", [])
    try:
        sc, miss = _compute_reliability_score(r)
        if r.get("reliability_score") != sc:
            r["reliability_score"] = sc
            changed = True
        # keep missing hints
        if r.get("reliability_missing") != miss:
            r["reliability_missing"] = miss
            changed = True
    except Exception:
        # do not block loading
        pass

    return r, changed


def _get_regs() -> List[Dict[str, Any]]:
    regs = _load_json(REG_FILE, [])
    if not isinstance(regs, list):
        return []
    changed = False
    out: List[Dict[str, Any]] = []
    for r in regs:
        if not isinstance(r, dict):
            continue
        rr, ch = _normalize_reg(r)
        out.append(rr)
        changed = changed or ch
    if changed:
        _save_json(REG_FILE, out)
    return out


def _save_regs(regs: List[Dict[str, Any]]) -> None:
    _save_json(REG_FILE, regs)


def _get_locked_user_ids(users: List[Dict[str, Any]]) -> set[str]:
    """Retourne les IDs d'utilisateurs agents/superviseurs qui ne peuvent
    pas être supprimés car ils ont déjà des dossiers validés ou ont validé
    des dossiers."""
    regs = _get_regs()
    locked: set[str] = set()
    for u in users:
        uid = u.get("id")
        role = u.get("role")
        if not uid or role not in ("agent", "supervisor"):
            continue

        # Agent : a au moins un dossier dont le statut est vérifié / approuvé / payé
        if role == "agent":
            for r in regs:
                if r.get("created_by") == uid:
                    st = _canon_status(r.get("status"))
                    if st in (STATUS_VERIFIED, STATUS_APPROVED, STATUS_PAID):
                        locked.add(uid)
                        break

        # Superviseur : a déjà validé un dossier
        elif role == "supervisor":
            for r in regs:
                if r.get("supervisor_verified_by") == uid or r.get("verified_by") == uid:
                    if _supervisor_mark(r):
                        locked.add(uid)
                        break
    return locked


def _strip_accents(s: str) -> str:
    s = unicodedata.normalize("NFKD", s or "")
    return "".join(ch for ch in s if not unicodedata.combining(ch))


def _norm_key(s: str) -> str:
    # Lower + accents removed + normalized spaces
    s2 = _strip_accents(s).lower()
    return " ".join((s2 or "").strip().split())


def _norm_cmp(s: Any) -> str:
    """Robust normalization for user-entered text comparisons."""
    return _norm_key(str(s or ""))


def _match_center_from_value(centers: List[Dict[str, Any]], value: Any) -> Optional[Dict[str, Any]]:
    """Find a center in referential by id or (accent/case-insensitive) name.

    Accepts values like:
      - center id (e.g. "c_001")
      - center name (e.g. "PLACE PUBLIQUE KODJOBOUE")
      - center name with suffix (e.g. "... / BV01")
      - shortened name matching the end of the official name (e.g. "Kodjoboue")
    """
    if value is None:
        return None
    raw = str(value).strip()
    if not raw:
        return None

    # Remove bureau suffix if present.
    base = raw.split("/")[0].strip()

    # First try exact id match.
    for c in centers:
        if str(c.get("id", "")).strip() == base:
            return c

    n_base = _norm_cmp(base)
    if not n_base:
        return None

    # Exact normalized name
    for c in centers:
        if _norm_cmp(c.get("name", "")) == n_base:
            return c

    # Fallback: treat a short value like "Kodjoboue" as matching the end of
    # "PLACE PUBLIQUE KODJOBOUE", etc.
    for c in centers:
        cname_norm = _norm_cmp(c.get("name", ""))
        if not cname_norm:
            continue
        if cname_norm.endswith(" " + n_base) or n_base.endswith(" " + cname_norm):
            return c

    return None

def _norm_text(s: str) -> str:
    # Legacy helper used in a few places (kept for compatibility)
    return (s or "").strip().lower()


def _norm_date_ymd(s: str) -> str:
    ss = (s or "").strip()
    if not ss:
        return ""
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%Y/%m/%d"):
        try:
            return datetime.strptime(ss, fmt).date().isoformat()
        except Exception:
            pass
    return ss


def _phone_digits(s: str) -> str:
    return "".join(ch for ch in (s or "") if ch.isdigit())


def _phone_is_valid_ci(s: str) -> bool:
    d = _phone_digits(s)
    # Côte d'Ivoire: 10 chiffres (nouveau plan de numérotation)
    return len(d) == 10 and d.startswith("0")


def _compute_reliability_score(reg: Dict[str, Any]) -> Tuple[int, List[str]]:
    """Retourne (score_sur_100, liste_des_manquants)."""
    missing: List[str] = []
    score = 0

    # 100 points, simple et lisible pour l'admin.
    if (reg.get("nom") or "").strip():
        score += 12
    else:
        missing.append("Nom")

    if (reg.get("prenoms") or "").strip():
        score += 12
    else:
        missing.append("Prénoms")

    if (reg.get("dob") or "").strip():
        score += 12
    else:
        missing.append("Date de naissance")

    if (reg.get("quartier") or "").strip():
        score += 10
    else:
        missing.append("Quartier")

    tel = (reg.get("telephone") or "").strip()
    if tel:
        score += 10
        if _phone_is_valid_ci(tel):
            score += 8
        else:
            missing.append("Téléphone invalide")
    else:
        missing.append("Téléphone")

    photos = reg.get("photos") or []
    if isinstance(photos, list) and len(photos) > 0:
        score += 10
    else:
        missing.append("Photo")

    if (reg.get("voter_number") or "").strip():
        score += 14
    else:
        missing.append("N° électeur")

    if (reg.get("polling_center") or "").strip():
        score += 6
    else:
        missing.append("Centre")

    if (reg.get("polling_station") or "").strip():
        score += 6
    else:
        missing.append("Bureau")

    score = max(0, min(100, int(score)))
    return score, missing


def _deepcopy_json(obj: Any) -> Any:
    try:
        return json.loads(json.dumps(obj, ensure_ascii=False))
    except Exception:
        return obj


def _diff_reg(before: Dict[str, Any], after: Dict[str, Any]) -> List[Dict[str, Any]]:
    fields = [
        "nom", "prenoms", "dob", "quartier", "telephone",
        "voter_number", "polling_center", "polling_station",
        "status", "notes", "qc_notes", "correction_reason",
    ]
    diffs: List[Dict[str, Any]] = []
    for f in fields:
        a = (after.get(f) if isinstance(after, dict) else None)
        b = (before.get(f) if isinstance(before, dict) else None)
        if (a or "") != (b or ""):
            diffs.append({"field": f, "from": b, "to": a})

    # Photos: log only count to avoid noise
    b_ph = before.get("photos") if isinstance(before.get("photos"), list) else []
    a_ph = after.get("photos") if isinstance(after.get("photos"), list) else []
    if len(a_ph) != len(b_ph):
        diffs.append({"field": "photos", "from": len(b_ph), "to": len(a_ph)})

    # Reliability score
    b_rs = before.get("reliability_score")
    a_rs = after.get("reliability_score")
    if a_rs != b_rs:
        diffs.append({"field": "reliability_score", "from": b_rs, "to": a_rs})

    return diffs


def _audit_reg_change(action: str, actor_id: str, before: Optional[Dict[str, Any]], after: Optional[Dict[str, Any]], extra: Optional[Dict[str, Any]] = None) -> None:
    details: Dict[str, Any] = dict(extra or {})
    tgt = after or before or {}
    if before is not None and after is not None:
        diffs = _diff_reg(before, after)
        if diffs:
            details["changes"] = diffs
    _audit(action, actor_id, "registration", str(tgt.get("id") or ""), details)


def _find_duplicates(
    nom: str,
    prenoms: str,
    dob: str,
    polling_center: str,
    regs: List[Dict[str, Any]],
    *,
    zone_id: Optional[str] = None,
    exclude_id: Optional[str] = None,
    strict_center: bool = False,
    limit: int = 10,
) -> List[Dict[str, Any]]:
    """Détection de doublons: nom + prénoms + DOB (+ centre si strict_center).

    - zone_id: si fourni, ne compare que dans la zone (sécurité/pertinence)
    - exclude_id: ignore un dossier (ex: édition)
    """
    nn = _norm_key(nom)
    pp = _norm_key(prenoms)
    dd = _norm_date_ymd(dob)
    cc = _norm_key(polling_center)

    if not (nn and pp and dd):
        return []

    matches: List[Dict[str, Any]] = []
    for r in regs:
        if not isinstance(r, dict):
            continue
        if exclude_id and str(r.get("id")) == str(exclude_id):
            continue
        if zone_id and str(r.get("zone_id") or "") != str(zone_id):
            continue

        same_name = _norm_key(r.get("nom") or "") == nn and _norm_key(r.get("prenoms") or "") == pp
        same_dob = _norm_date_ymd(r.get("dob") or "") == dd

        if not (same_name and same_dob):
            continue

        if strict_center:
            if _norm_key(r.get("polling_center") or "") != cc or not cc:
                continue

        matches.append(r)
        if len(matches) >= limit:
            break

    return matches


# ----------------------------
# Uploads (photos)
# ----------------------------
# ----------------------------

def _allowed_upload(filename: str) -> bool:
    ext = os.path.splitext(filename.lower())[1]
    return ext in ALLOWED_UPLOAD_EXT


def _save_upload(file_storage) -> str:
    """Save upload and return stored filename (relative)."""
    filename = secure_filename(file_storage.filename or "")
    if not filename:
        raise ValueError("Nom de fichier invalide")
    if not _allowed_upload(filename):
        raise ValueError("Format non autorisé (jpg, png, pdf)")

    # size check
    file_storage.stream.seek(0, os.SEEK_END)
    size = file_storage.stream.tell()
    file_storage.stream.seek(0)
    if size > MAX_UPLOAD_MB * 1024 * 1024:
        raise ValueError(f"Fichier trop volumineux (max {MAX_UPLOAD_MB} MB)")

    ext = os.path.splitext(filename)[1].lower()
    stored = f"{uuid.uuid4().hex}{ext}"
    path = os.path.join(UPLOADS_DIR, stored)
    file_storage.save(path)
    return stored


def _can_view_reg(u: Dict[str, Any], reg: Dict[str, Any]) -> bool:
    role = u.get("role")
    if role == "admin":
        return True
    if role == "supervisor":
        return reg.get("zone_id") == u.get("zone_id")
    if role == "agent":
        return reg.get("created_by") == u.get("id")
    return False


# ----------------------------
# Payroll (paiement agents, stockage JSON)
# ----------------------------

def _get_payroll() -> List[Dict[str, Any]]:
    items = _load_json(PAYROLL_FILE, [])
    if not isinstance(items, list):
        return []

    changed = False
    for it in items:
        if not isinstance(it, dict):
            continue
        it.setdefault("type", "PAYSLIP")  # PAYSLIP or ADVANCE
        if "payment_number" not in it:
            it["payment_number"] = it.get("id", "")
            changed = True
        it.setdefault("status", "GENERATED")
        it.setdefault("paid_at", "")
        it.setdefault("paid_by", "")
        it.setdefault("notes", "")
        it.setdefault("is_locked", False)
        it.setdefault("locked_at", "")
        it.setdefault("advance_amount", 0)
        it.setdefault("gross_amount", int(it.get("amount", 0) or 0))
        it.setdefault("balance_amount", int(it.get("amount", 0) or 0))
        it.setdefault("created_at", it.get("generated_at", "") or _now_iso())

    if changed:
        _save_json(PAYROLL_FILE, items)
    return items


def _save_payroll(items: List[Dict[str, Any]]) -> None:
    _save_json(PAYROLL_FILE, items)


def _next_payment_number(items: List[Dict[str, Any]]) -> str:
    max_n = 0
    for it in items:
        pn = (it.get("payment_number") or "").strip().upper()
        if pn.startswith("PAY-"):
            try:
                n = int(pn.split("-")[-1])
                max_n = max(max_n, n)
            except Exception:
                continue
    return f"PAY-{max_n + 1:06d}"


def _dt_from_iso(s: str) -> datetime:
    try:
        return datetime.fromisoformat(s)
    except Exception:
        return datetime.fromisoformat(s.replace("Z", "+00:00"))



# --- Campaign window helpers (pilotage/map) ---
def _to_utc(dt):
    """Ensure datetime is timezone-aware in UTC."""
    if dt is None:
        return None
    try:
        if getattr(dt, "tzinfo", None) is None:
            return dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        return None


def _safe_dt_any(s):
    """Parse iso datetime safely and return UTC aware dt (or None)."""
    if not s:
        return None
    try:
        return _to_utc(_dt_from_iso(str(s)))
    except Exception:
        try:
            return _to_utc(datetime.fromisoformat(str(s)))
        except Exception:
            return None


def _campaign_window(settings: dict):
    """Compute campaign date window from settings (UTC)."""
    campaign_start = (settings.get("campaign_start_date") or "").strip()
    campaign_end = (settings.get("campaign_end_date") or "").strip()
    start_dt = None
    end_dt = None
    if campaign_start:
        try:
            start_dt = _to_utc(datetime.fromisoformat(campaign_start))
        except Exception:
            start_dt = None
    if campaign_end:
        try:
            end_day = _to_utc(datetime.fromisoformat(campaign_end))
            if end_day:
                # include full day
                end_dt = end_day + timedelta(days=1) - timedelta(seconds=1)
        except Exception:
            end_dt = None
    return start_dt, end_dt


def _in_window(r: dict, start_dt, end_dt) -> bool:
    """Check if registration record is inside campaign window."""
    if not start_dt and not end_dt:
        return True
    dt = _safe_dt_any(r.get("created_at")) or _safe_dt_any(r.get("updated_at"))
    if not dt:
        return True
    if start_dt and dt < start_dt:
        return False
    if end_dt and dt > end_dt:
        return False
    return True


def _is_real(r: dict) -> bool:
    """Exclude drafts from operational metrics."""
    return r.get("status") != STATUS_DRAFT

def _periods_for_user(user_id: str, regs: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    all_dts = [_dt_from_iso(r["created_at"]) for r in regs if r.get("created_at")]
    if not all_dts:
        return []

    mine = [r for r in regs if r.get("created_by") == user_id and r.get("created_at")]
    if not mine:
        return []

    anchor = min(all_dts).date()
    max_dt = max(_dt_from_iso(r["created_at"]) for r in mine)

    start = datetime(anchor.year, anchor.month, anchor.day, tzinfo=timezone.utc)
    periods: List[Dict[str, Any]] = []
    while start <= max_dt + timedelta(days=1):
        end = start + timedelta(days=_pay_period_days())
        periods.append({
            "start": start,
            "end": end,
            "start_iso": start.date().isoformat(),
            "end_iso": end.date().isoformat(),
        })
        start = end
    return periods


def _count_regs_in_period(user_id: str, regs: List[Dict[str, Any]], start: datetime, end: datetime) -> int:
    n = 0
    for r in regs:
        if r.get("created_by") != user_id:
            continue
        if r.get("status") == STATUS_DRAFT:
            continue
        ca = r.get("created_at") or ""
        if not ca:
            continue
        dt = _dt_from_iso(ca)
        if start <= dt < end:
            n += 1
    return n



def _count_approved_regs_in_period(user_id: str, regs: List[Dict[str, Any]], start: datetime, end: datetime) -> int:
    """Nombre de dossiers approuvés (STATUT APPROVED) pour un agent sur une période."""
    n = 0
    for r in regs:
        if r.get("created_by") != user_id:
            continue
        if r.get("status") != STATUS_APPROVED:
            continue
        ca = r.get("created_at") or ""
        if not ca:
            continue
        dt = _dt_from_iso(ca)
        if start <= dt < end:
            n += 1
    return n


def _sum_advances(user_id: str, items: List[Dict[str, Any]], start_iso: str, end_iso: str) -> int:
    """Sum advances for a given pay period.

    Important: in the UI, periods are displayed as inclusive end dates
    (end_exclusive - 1 day). Some previously saved advances therefore
    contain an inclusive period_end (YYYY-MM-DD) instead of the internal
    end_exclusive date used by pay periods.

    To avoid mismatches (and missing deductions), we accept BOTH forms.
    """
    total = 0
    try:
        end_inclusive = (date.fromisoformat(end_iso) - timedelta(days=1)).isoformat()
    except Exception:
        end_inclusive = ""

    for it in items:
        if it.get("type") != "ADVANCE":
            continue
        if it.get("user_id") != user_id:
            continue
        if it.get("period_start") != start_iso:
            continue

        pe = (it.get("period_end") or "").strip()
        # accept end_exclusive OR end_inclusive
        if pe == end_iso or (end_inclusive and pe == end_inclusive):
            total += int(it.get("amount", 0) or 0)

    return total


def _find_payslip(user_id: str, start_iso: str, end_iso: str, items: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    """Return the *primary* payslip (type PAYSLIP) for a period.

    Notes:
    - A period can also have one or several supplements (type PAYSLIP_SUPP).
      Those are handled via `_find_payslips()`.
    - If multiple primary payslips exist (legacy), the most recent one wins.
    """
    candidates: List[Dict[str, Any]] = []
    for it in items:
        if it.get("type") != "PAYSLIP":
            continue
        if it.get("user_id") != user_id:
            continue
        if it.get("period_start") != start_iso or it.get("period_end") != end_iso:
            continue
        candidates.append(it)

    if not candidates:
        return None

    candidates.sort(key=lambda x: (x.get("generated_at") or x.get("created_at") or ""))
    return candidates[-1]


PAYSLIP_TYPES = ("PAYSLIP", "PAYSLIP_SUPP")


def _find_payslips(user_id: str, start_iso: str, end_iso: str, items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Return ALL payslips (primary + supplements) for a period."""
    slips = [
        it
        for it in items
        if (it.get("type") in PAYSLIP_TYPES)
        and it.get("user_id") == user_id
        and it.get("period_start") == start_iso
        and it.get("period_end") == end_iso
    ]
    slips.sort(key=lambda x: (x.get("generated_at") or x.get("created_at") or ""))
    return slips


def _calc_amount(count: int) -> int:
    return int(count) * int(_pay_rate_cfa())


def _format_money_cfa(x: int) -> str:
    s = f"{int(x):,}".replace(",", " ")
    return f"{s} F CFA"


def _period_label(start_iso: str, end_iso: str) -> str:
    try:
        s = date.fromisoformat(start_iso)
        e = date.fromisoformat(end_iso) - timedelta(days=1)
        return f"{s.strftime('%d/%m/%Y')} → {e.strftime('%d/%m/%Y')}"
    except Exception:
        return f"{start_iso} → {end_iso}"


# ----------------------------
# SMS
# ----------------------------

def _get_sms_config() -> Dict[str, Any]:
    return _load_json(
        SMS_CONFIG_FILE,
        {
            "mode": "dry_run",
            "sender_id": "Elections2028",
            "http_json": {"url": "", "token": "", "to_field": "to", "message_field": "message", "sender_field": "sender"},
        },
    )


def _save_sms_config(cfg: Dict[str, Any]) -> None:
    _save_json(SMS_CONFIG_FILE, cfg)


def _get_sms_campaigns() -> List[Dict[str, Any]]:
    data = _load_json(SMS_CAMPAIGNS_FILE, [])
    return data if isinstance(data, list) else []


def _save_sms_campaigns(camps: List[Dict[str, Any]]) -> None:
    _save_json(SMS_CAMPAIGNS_FILE, camps)


def _get_sms_outbox() -> List[Dict[str, Any]]:
    data = _load_json(SMS_OUTBOX_FILE, [])
    return data if isinstance(data, list) else []


def _save_sms_outbox(outbox: List[Dict[str, Any]]) -> None:
    _save_json(SMS_OUTBOX_FILE, outbox)


def _get_sms_logs() -> List[Dict[str, Any]]:
    data = _load_json(SMS_LOGS_FILE, [])
    return data if isinstance(data, list) else []


def _save_sms_logs(logs: List[Dict[str, Any]]) -> None:
    _save_json(SMS_LOGS_FILE, logs)


def _http_json_send(url: str, token: str, payload: Dict[str, Any]) -> Dict[str, Any]:
    import urllib.request
    import urllib.error

    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST")
    req.add_header("Content-Type", "application/json")
    if token:
        req.add_header("Authorization", f"Bearer {token}")

    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            body = resp.read().decode("utf-8", errors="ignore")
            return {"ok": True, "status": resp.status, "body": body[:500]}
    except urllib.error.HTTPError as e:
        try:
            body = e.read().decode("utf-8", errors="ignore")
        except Exception:
            body = str(e)
        return {"ok": False, "status": getattr(e, "code", 0), "body": body[:500]}
    except Exception as e:
        return {"ok": False, "status": 0, "body": str(e)[:500]}


def _send_sms(to_phone: str, message: str) -> Dict[str, Any]:
    cfg = _get_sms_config()
    mode = (cfg.get("mode") or "dry_run").lower()

    if mode == "http_json":
        http_cfg = cfg.get("http_json") or {}
        url = (http_cfg.get("url") or "").strip()
        if not url:
            return {"ok": False, "status": 0, "body": "sms_config.json: http_json.url vide"}
        token = (http_cfg.get("token") or "").strip()
        to_field = http_cfg.get("to_field") or "to"
        msg_field = http_cfg.get("message_field") or "message"
        sender_field = http_cfg.get("sender_field") or "sender"
        payload = {
            to_field: to_phone,
            msg_field: message,
            sender_field: cfg.get("sender_id") or "",
        }
        return _http_json_send(url, token, payload)

    return {"ok": True, "status": 0, "body": "DRY_RUN (aucun SMS envoyé)"}


def _process_due_campaigns(actor_id: str) -> None:
    """Process scheduled campaigns (best-effort). Called on admin/supervisor SMS pages."""
    now = datetime.now(timezone.utc)
    camps = _get_sms_campaigns()
    if not camps:
        return

    regs = _get_regs()
    logs = _get_sms_logs()

    changed = False
    sent_this_request = 0

    for c in camps:
        if sent_this_request >= MAX_SMS_SEND_PER_REQUEST:
            break
        if c.get("status") in ("DONE", "CANCELLED"):
            continue
        sched = (c.get("scheduled_at") or "").strip()
        if not sched:
            continue
        try:
            sched_dt = _dt_from_iso(sched)
        except Exception:
            continue
        if sched_dt > now:
            continue

        # Ready to send (or resume)
        c.setdefault("sent_count", 0)
        c.setdefault("total_count", 0)
        c.setdefault("status", "SCHEDULED")

        # Build targets from campaign filters
        zone_id = (c.get("zone_id") or "").strip()
        center = (c.get("polling_center") or "").strip()
        status_filter = (c.get("status_filter") or "").strip()  # APPROVED/VERIFIED/PENDING etc
        only_missing_voter = bool(c.get("only_missing_voter"))

        targets = []
        for r in regs:
            if zone_id and r.get("zone_id") != zone_id:
                continue
            if center and (r.get("polling_center") or "") != center:
                continue
            if status_filter and r.get("status") != status_filter:
                continue
            if only_missing_voter and (r.get("voter_number") or "").strip():
                continue
            phone = (r.get("telephone") or "").strip()
            if not phone:
                continue
            targets.append(r)

        c["total_count"] = len(targets)
        msg = (c.get("message") or "").strip()
        if not msg:
            c["status"] = "FAILED"
            c["error"] = "Message vide"
            changed = True
            continue

        # resume at offset
        offset = int(c.get("sent_count", 0) or 0)
        remaining = targets[offset:]

        if not remaining:
            c["status"] = "DONE"
            c["finished_at"] = _now_iso()
            changed = True
            continue

        c["status"] = "SENDING"
        changed = True

        for r in remaining:
            if sent_this_request >= MAX_SMS_SEND_PER_REQUEST:
                break

            res = _send_sms((r.get("telephone") or "").strip(), msg)
            logs.append({
                "id": str(uuid.uuid4()),
                "at": _now_iso(),
                "campaign_id": c.get("id"),
                "reg_id": r.get("id"),
                "to": (r.get("telephone") or "").strip(),
                "message": msg,
                "ok": bool(res.get("ok")),
                "provider_status": res.get("status"),
                "provider_body": res.get("body"),
            })
            r["sms_last_at"] = _now_iso()
            c["sent_count"] = int(c.get("sent_count", 0) or 0) + 1
            sent_this_request += 1

        if c.get("sent_count", 0) >= c.get("total_count", 0):
            c["status"] = "DONE"
            c["finished_at"] = _now_iso()

    if changed:
        _save_sms_campaigns(camps)
        _save_sms_logs(logs)
        _save_regs(regs)
        _audit("sms.process_due", actor_id, "sms", "campaigns", {"sent": sent_this_request})


# ----------------------------
# Session helpers
# ----------------------------

def current_user() -> Optional[Dict[str, Any]]:
    uid = session.get("user_id")
    if not uid:
        return None
    for u in _get_users():
        if u.get("id") == uid and u.get("is_active", True):
            return u
    return None


def _is_admin() -> bool:
    """Compat helper: certaines routes utilisent _is_admin()."""
    u = current_user()
    return bool(u) and u.get("role") == "admin"



def _supervisor_mark(reg: dict, st: str | None = None) -> bool:
    # True si le superviseur a 'Vérifié' ce dossier
    if st is None:
        st = _canon_status(reg.get('status'))
    return bool(
        reg.get('supervisor_verified')
        or reg.get('supervisor_verified_at')
        or reg.get('verified_by')
        or reg.get('verified_at')
        or (reg.get('supervisor_status') == STATUS_VERIFIED)
        or (st == STATUS_VERIFIED)
    )

def _admin_done(reg: dict) -> bool:
    # True si l'admin a déjà pris une décision finale sur ce dossier
    st = _canon_status(reg.get('status'))
    if st in (STATUS_APPROVED, STATUS_REJECTED, STATUS_PAID):
        return True

    if _norm_bool(reg.get('admin_approved')):
        return True

    if reg.get('admin_approved_by') or reg.get('admin_approved_at'):
        return True
    if reg.get('admin_rejected_by') or reg.get('admin_rejected_at'):
        return True

    # legacy fields
    if reg.get('approved_by') or reg.get('approved_at'):
        return True
    if reg.get('rejected_by') or reg.get('rejected_at'):
        return True

    return False


def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        if not current_user():
            return redirect(url_for("login", next=request.path))
        return fn(*args, **kwargs)

    return wrapper


def role_required(*roles):
    def decorator(fn):
        @wraps(fn)
        def wrapper(*args, **kwargs):
            u = current_user()
            if not u:
                return redirect(url_for("login", next=request.path))
            if u.get("role") not in roles:
                abort(403)
            return fn(*args, **kwargs)

        return wrapper

    return decorator


# ----------------------------
# CSRF (minimal)
# ----------------------------

def _csrf_get_token() -> str:
    token = session.get("csrf_token")
    if not token:
        token = secrets.token_urlsafe(32)
        session["csrf_token"] = token
    return token


def _csrf_validate() -> bool:
    form_token = request.form.get("csrf_token", "")
    return bool(form_token) and form_token == session.get("csrf_token")


@app.context_processor
def inject_globals():
    settings = _get_settings()
    return {
        "app_name": APP_NAME,
        "app_version": APP_VERSION,
        "csrf_token": _csrf_get_token,
        "me": current_user(),
        "zones_map": {z["id"]: z for z in _get_zones()},
        "format_money_cfa": _format_money_cfa,
        "pay_rate_cfa": _pay_rate_cfa(),
        "period_label": _period_label,
        "double_approval": bool(settings.get("double_approval")),
        "STATUS": {
            "DRAFT": STATUS_DRAFT,
            "PENDING": STATUS_PENDING,
            "NEEDS_CORRECTION": STATUS_NEEDS_CORRECTION,
            "VERIFIED": STATUS_VERIFIED,
            "APPROVED": STATUS_APPROVED,
            "REJECTED": STATUS_REJECTED,
        },
    }


# ----------------------------
# Utility
# ----------------------------

def _format_date(d: str) -> str:
    if not d:
        return "—"
    try:
        return date.fromisoformat(d).strftime("%d/%m/%Y")
    except Exception:
        return d


def _safe_filename(name: str) -> str:
    keep = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"
    return "".join([c if c in keep else "_" for c in (name or "file")])


# ----------------------------
# Auth routes
# ----------------------------

@app.route("/")
def index():
    u = current_user()
    if not u:
        return redirect(url_for("login"))
    if u.get("role") == "admin":
        return redirect(url_for("admin_dashboard"))
    if u.get("role") == "supervisor":
        return redirect(url_for("supervisor_dashboard"))
    if u.get("role") == "agent":
        return redirect(url_for("agent_dashboard"))
    return redirect(url_for("login"))


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = (request.form.get("username") or "").strip()
        password = request.form.get("password") or ""
        next_url = (request.args.get("next") or request.form.get("next") or "").strip()

        for u in _get_users():
            if u.get("username") == username and u.get("is_active", True):
                if check_password_hash(u.get("password_hash", ""), password):
                    session["user_id"] = u["id"]
                    _csrf_get_token()
                    _audit("auth.login", u["id"], "user", u["id"], {})
                    flash("Connexion réussie.", "success")
                    if next_url:
                        return redirect(next_url)
                    return redirect(url_for("index"))

        flash("Identifiants invalides.", "danger")
        return render_template("login.html", next=next_url)

    return render_template("login.html", next=(request.args.get("next") or ""))


@app.route("/logout")
def logout():
    u = current_user()
    if u:
        _audit("auth.logout", u["id"], "user", u["id"], {})
    session.clear()
    flash("Déconnexion.", "success")
    return redirect(url_for("login"))


# ----------------------------
# Admin routes
# ----------------------------

@app.route("/admin")
@role_required("admin")
def admin_dashboard():
    users = _get_users()
    regs = _get_regs()
    zones = _get_active_zones()
    obj = _get_objectives_map()
    zone_objectives = obj.get("zones", {}) if isinstance(obj, dict) else {}
    user_objectives = obj.get("users", {}) if isinstance(obj, dict) else {}

    counts = {
        "agents": sum(1 for u in users if u.get("role") == "agent"),
        "supervisors": sum(1 for u in users if u.get("role") == "supervisor"),
        "registrations": len(regs),
        "draft": sum(1 for r in regs if r.get("status") == STATUS_DRAFT),
        "pending": sum(1 for r in regs if r.get("status") == STATUS_PENDING),
        "needs_correction": sum(1 for r in regs if r.get("status") == STATUS_NEEDS_CORRECTION),
        "verified": sum(1 for r in regs if r.get("status") == STATUS_VERIFIED),
        "approved": sum(1 for r in regs if r.get("status") == STATUS_APPROVED),
        "rejected": sum(1 for r in regs if r.get("status") == STATUS_REJECTED),
    }

    # performance table by agent
    agents = [u for u in users if u.get("role") == "agent" and u.get("is_active", True)]
    perf = []
    for a in agents:
        mine = [r for r in regs if r.get("created_by") == a.get("id")]
        perf.append({
            "agent": a,
            "zone": _zone_name(a.get("zone_id")),
            "total": len(mine),
            "pending": sum(1 for r in mine if r.get("status") == STATUS_PENDING),
            "needs_correction": sum(1 for r in mine if r.get("status") == STATUS_NEEDS_CORRECTION),
            "verified": sum(1 for r in mine if r.get("status") == STATUS_VERIFIED),
            "approved": sum(1 for r in mine if r.get("status") == STATUS_APPROVED),
            "rejected": sum(1 for r in mine if r.get("status") == STATUS_REJECTED),
        })
    perf = sorted(perf, key=lambda x: x["total"], reverse=True)

    # zone progress vs objective
    zone_rows = []
    for z in zones:
        zid = z.get("id")
        total_zone = sum(1 for r in regs if r.get("zone_id") == zid and r.get("status") != STATUS_DRAFT)
        target = int((zone_objectives.get(zid) or {}).get("target", 0) or 0)
        pct = 0
        if target > 0:
            pct = int((total_zone / target) * 100)
        zone_rows.append({"zone": z, "total": total_zone, "target": target, "pct": pct})

    zone_rows = sorted(zone_rows, key=lambda x: x["total"], reverse=True)

    return render_template(
        "admin/dashboard.html",
        counts=counts,
        perf=perf,
        zone_rows=zone_rows,
    )


@app.route("/admin/zones", methods=["GET", "POST"])
@role_required("admin")
def admin_zones():
    # Keep all zones in storage (even when "deleted") so existing records can still
    # resolve their zone name in history/audit. In the UI we list only active zones.
    zones_all = _get_zones()
    zones = [z for z in zones_all if z.get("active", True)]
    if request.method == "POST":
        if not _csrf_validate():
            abort(400)
        action = (request.form.get("action") or "add").strip().lower()

        # 1) Add zone
        if action == "add":
            name = (request.form.get("name") or "").strip()
            if not name:
                flash("Nom de zone requis.", "warning")
                return redirect(url_for("admin_zones"))
            if any((z.get("name", "").lower() == name.lower()) for z in zones_all):
                flash("Cette zone existe déjà.", "warning")
                return redirect(url_for("admin_zones"))
            new_zone = {"id": str(uuid.uuid4()), "name": name, "active": True}
            zones_all.append(new_zone)
            _save_zones(zones_all)
            _audit("zone.create", current_user()["id"], "zone", new_zone["id"], {"name": name})
            flash("Zone ajoutée.", "success")
            return redirect(url_for("admin_zones"))

        # 2) Update zone name
        if action == "update":
            zone_id = (request.form.get("zone_id") or "").strip()
            name = (request.form.get("name") or "").strip()
            if not zone_id:
                flash("Zone introuvable.", "warning")
                return redirect(url_for("admin_zones"))
            if not name:
                flash("Nom de zone requis.", "warning")
                return redirect(url_for("admin_zones"))
            z = next((x for x in zones_all if x.get("id") == zone_id), None)
            if not z:
                flash("Zone introuvable.", "warning")
                return redirect(url_for("admin_zones"))
            if any((x.get("id") != zone_id and x.get("name", "").lower() == name.lower()) for x in zones_all):
                flash("Une autre zone porte déjà ce nom.", "warning")
                return redirect(url_for("admin_zones"))
            old_name = z.get("name")
            z["name"] = name
            _save_zones(zones_all)
            _audit("zone.update", current_user()["id"], "zone", zone_id, {"from": old_name, "to": name})
            flash("Zone modifiée.", "success")
            return redirect(url_for("admin_zones"))

        # 3) Delete (soft delete) zone
        if action == "delete":
            zone_id = (request.form.get("zone_id") or "").strip()
            z = next((x for x in zones_all if x.get("id") == zone_id), None)
            if not z:
                flash("Zone introuvable.", "warning")
                return redirect(url_for("admin_zones"))
            z["active"] = False
            _save_zones(zones_all)
            _audit("zone.delete", current_user()["id"], "zone", zone_id, {"active": False})
            flash("Zone supprimée.", "success")
            return redirect(url_for("admin_zones"))

        flash("Action invalide.", "warning")
        return redirect(url_for("admin_zones"))

    return render_template("admin/zones.html", zones=zones)


@app.route("/admin/pilotage")
@role_required("admin")
def admin_pilotage():
    zones = _get_active_zones()
    regs = _get_regs()
    users = _get_users()
    settings = _get_settings()
    centers_map = _get_centers_map()

    obj = _get_objectives_map()
    zone_objectives = obj.get("zones", {}) if isinstance(obj, dict) else {}
    user_objectives = obj.get("users", {}) if isinstance(obj, dict) else {}

    # Pilotage settings (safe defaults)
    inactivity_hours = int(settings.get("pilotage_inactivity_hours", 6) or 6)
    spike_window_min = int(settings.get("pilotage_spike_window_minutes", 60) or 60)
    spike_multiplier = float(settings.get("pilotage_spike_multiplier", 3) or 3)
    spike_min_abs = int(settings.get("pilotage_spike_min_abs", 10) or 10)
    behind_slack = int(settings.get("pilotage_behind_slack_pct", 10) or 10)

    campaign_start = (settings.get("campaign_start_date") or "").strip()
    campaign_end = (settings.get("campaign_end_date") or "").strip()

    def _safe_dt(s: Any):
        try:
            return _dt_from_iso(s) if s else None
        except Exception:
            return None

    now = datetime.now(timezone.utc)

    # Campaign window filter (optional)
    start_dt = None
    end_dt = None
    if campaign_start:
        try:
            start_dt = datetime.fromisoformat(campaign_start).replace(tzinfo=timezone.utc)
        except Exception:
            start_dt = None
    if campaign_end:
        try:
            end_dt = datetime.fromisoformat(campaign_end).replace(tzinfo=timezone.utc) + timedelta(days=1) - timedelta(seconds=1)
        except Exception:
            end_dt = None

    def _in_window(r: Dict[str, Any]) -> bool:
        if not start_dt and not end_dt:
            return True
        dt = _safe_dt(r.get("created_at")) or _safe_dt(r.get("updated_at"))
        if not dt:
            return True
        if start_dt and dt < start_dt:
            return False
        if end_dt and dt > end_dt:
            return False
        return True

    def _is_real(r: Dict[str, Any]) -> bool:
        return r.get("status") != STATUS_DRAFT

    # ---------- Zone stats ----------
    zone_rows = []
    for z in zones:
        zid = z.get("id")
        zregs = [r for r in regs if r.get("zone_id") == zid and _is_real(r) and _in_window(r)]
        total = len(zregs)
        by_status = {
            "pending": sum(1 for r in zregs if r.get("status") == STATUS_PENDING),
            "corriger": sum(1 for r in zregs if r.get("status") == STATUS_NEEDS_CORRECTION),
            "verifies": sum(1 for r in zregs if r.get("status") == STATUS_VERIFIED),
            "approuves": sum(1 for r in zregs if r.get("status") == STATUS_APPROVED),
            "rejetes": sum(1 for r in zregs if r.get("status") == STATUS_REJECTED),
        }
        target = int((zone_objectives.get(str(zid)) or {}).get("target", 0) or 0)
        pct = int((total / target) * 100) if target else 0
        zone_rows.append({
            "zone": z,
            "total": total,
            "target": target,
            "pct": pct,
            "by_status": by_status,
        })

    # sort by name
    zone_rows.sort(key=lambda x: (x["zone"].get("name") or "").lower())

    # ---------- Zone detail (centres / bureaux) ----------
    zone_id = (request.args.get("zone") or "").strip()
    zone_detail = None
    if zone_id:
        z = next((z for z in zones if z.get("id") == zone_id), None)
        if z:
            zregs = [r for r in regs if r.get("zone_id") == zone_id and _is_real(r) and _in_window(r)]
            centers = centers_map.get(zone_id) or centers_map.get("_default") or []
            # Map center name -> centers config
            cfg_by_name = {c.get("name"): c for c in centers}
            # seen centers from data
            names = sorted(set([r.get("polling_center") for r in zregs if r.get("polling_center")]))
            # merge cfg names to show zeros too
            for c in centers:
                if c.get("name") and c.get("name") not in names:
                    names.append(c.get("name"))
            names = [n for n in names if n]
            names.sort(key=lambda s: s.lower())

            center_rows = []
            for cname in names:
                cregs = [r for r in zregs if (r.get("polling_center") or "") == cname]
                ctotal = len(cregs)
                cby = {
                    "pending": sum(1 for r in cregs if r.get("status") == STATUS_PENDING),
                    "corriger": sum(1 for r in cregs if r.get("status") == STATUS_NEEDS_CORRECTION),
                    "verifies": sum(1 for r in cregs if r.get("status") == STATUS_VERIFIED),
                    "approuves": sum(1 for r in cregs if r.get("status") == STATUS_APPROVED),
                    "rejetes": sum(1 for r in cregs if r.get("status") == STATUS_REJECTED),
                }

                bureaux_cfg = (cfg_by_name.get(cname) or {}).get("bureaux") or []
                bureau_names = []
                for b in bureaux_cfg:
                    # Compat : certains référentiels stockent les bureaux
                    # comme liste de chaînes ("BV01") au lieu d'objets.
                    if isinstance(b, dict):
                        bn = b.get("name") or b.get("id")
                    else:
                        bn = str(b) if b is not None else ""
                    bn = (bn or "").strip()
                    if bn:
                        bureau_names.append(bn)
                # add those from data
                seen_b = sorted(set([r.get("polling_station") for r in cregs if r.get("polling_station")]))
                for bn in seen_b:
                    if bn and bn not in bureau_names:
                        bureau_names.append(bn)
                bureau_names = [bn for bn in bureau_names if bn]
                bureau_names.sort(key=lambda s: s.lower())

                bureau_rows = []
                for bn in bureau_names:
                    bregs = [r for r in cregs if (r.get("polling_station") or "") == bn]
                    btotal = len(bregs)
                    bureau_rows.append({
                        "name": bn,
                        "total": btotal,
                        "pending": sum(1 for r in bregs if r.get("status") == STATUS_PENDING),
                        "corriger": sum(1 for r in bregs if r.get("status") == STATUS_NEEDS_CORRECTION),
                        "verifies": sum(1 for r in bregs if r.get("status") == STATUS_VERIFIED),
                        "approuves": sum(1 for r in bregs if r.get("status") == STATUS_APPROVED),
                        "rejetes": sum(1 for r in bregs if r.get("status") == STATUS_REJECTED),
                    })

                center_rows.append({
                    "name": cname,
                    "total": ctotal,
                    "by_status": cby,
                    "bureaux": bureau_rows,
                })

            zone_detail = {
                "zone": z,
                "centres": center_rows,
            }

    # ---------- Objectives & gauges (per agent / supervisor) ----------
    # Si une zone est sélectionnée, on n'affiche que les agents/superviseurs de cette zone.
    zone_filter = zone_id or None
    target_users = [
        u for u in users
        if u.get("role") in ("agent", "supervisor")
        and (not zone_filter or (u.get("zone_id") or "") == zone_filter)
    ]

    gauges = []
    for u in target_users:
        uid = u.get("id")
        role = u.get("role")
        target = int((user_objectives.get(str(uid)) or {}).get("target", 0) or 0)

        if role == "agent":
            done = sum(
                1
                for r in regs
                if r.get("created_by") == uid
                and _is_real(r)
                and _in_window(r)
                and (not zone_filter or (r.get("zone_id") or "") == zone_filter)
            )
        else:
            done = sum(
                1
                for r in regs
                if r.get("verified_by") == uid
                and r.get("status") in (STATUS_VERIFIED, STATUS_APPROVED)
                and _in_window(r)
                and (not zone_filter or (r.get("zone_id") or "") == zone_filter)
            )

        pct = int((done / target) * 100) if target else 0
        gauges.append({"user": u, "role": role, "target": target, "done": done, "pct": pct})

    gauges.sort(key=lambda x: ((x["role"] or ""), (x["user"].get("display_name") or "").lower()))

    # ---------- Alerts ----------
    alerts = {"zones_en_retard": [], "agents_inactifs": [], "pics_anormaux": []}

    # Zone behind: only if campaign dates are set and at least 2 days window
    if start_dt and end_dt and end_dt > start_dt and (end_dt - start_dt).days >= 2:
        elapsed = (now - start_dt).total_seconds()
        total_span = (end_dt - start_dt).total_seconds()
        expected_pct = int(max(0, min(100, (elapsed / total_span) * 100)))
        for zr in zone_rows:
            target = zr["target"]
            if target <= 0:
                continue
            actual_pct = int((zr["total"] / target) * 100)
            if actual_pct + behind_slack < expected_pct:
                alerts["zones_en_retard"].append({
                    "zone": zr["zone"],
                    "expected_pct": expected_pct,
                    "actual_pct": actual_pct,
                    "total": zr["total"],
                    "target": target,
                })

    # Agent inactivity
    threshold = now - timedelta(hours=inactivity_hours)
    audit = _load_json(AUDIT_FILE, default=[])
    for u in [u for u in users if u.get("role") == "agent"]:
        uid = u.get("id")
        times = []

        # registrations created by agent
        for r in regs:
            if r.get("created_by") == uid:
                times.append(_safe_dt(r.get("updated_at")) or _safe_dt(r.get("created_at")))

        # audit events by agent
        for a in audit:
            if a.get("actor_id") == uid:
                times.append(_safe_dt(a.get("at")))

        times = [t for t in times if t]
        last_seen = max(times) if times else None
        if last_seen and last_seen < threshold:
            hours = int((now - last_seen).total_seconds() // 3600)
            alerts["agents_inactifs"].append({"user": u, "last_seen": last_seen.isoformat(), "hours": hours})

    alerts["agents_inactifs"].sort(key=lambda x: x["hours"], reverse=True)

    # Spikes (pics anormaux) - per agent & per zone, based on registrations created
    window = timedelta(minutes=spike_window_min)
    window_start = now - window
    baseline_span = timedelta(hours=24)
    baseline_start = now - baseline_span

    def _count_in_range(items, start, end):
        c = 0
        for dt in items:
            if dt and start <= dt <= end:
                c += 1
        return c

    # per agent
    for u in [u for u in users if u.get("role") == "agent"]:
        uid = u.get("id")
        dts = []
        for r in regs:
            if r.get("created_by") == uid and _is_real(r):
                dt = _safe_dt(r.get("created_at"))
                if dt:
                    dts.append(dt)
        if not dts:
            continue
        recent = _count_in_range(dts, window_start, now)
        if recent <= 0:
            continue
        # baseline: average per window over last 24h excluding current window
        baseline_dts = [dt for dt in dts if baseline_start <= dt < window_start]
        baseline_count = len(baseline_dts)
        num_windows = max(1, int(baseline_span.total_seconds() // window.total_seconds()))
        baseline_avg = baseline_count / num_windows
        if recent >= max(spike_min_abs, int(math.ceil(baseline_avg * spike_multiplier))):
            alerts["pics_anormaux"].append({
                "type": "agent",
                "label": u.get("display_name"),
                "recent": recent,
                "baseline": round(baseline_avg, 2),
                "window_min": spike_window_min,
            })

    # per zone
    for z in zones:
        zid = z.get("id")
        dts = []
        for r in regs:
            if r.get("zone_id") == zid and _is_real(r):
                dt = _safe_dt(r.get("created_at"))
                if dt:
                    dts.append(dt)
        if not dts:
            continue
        recent = _count_in_range(dts, window_start, now)
        if recent <= 0:
            continue
        baseline_dts = [dt for dt in dts if baseline_start <= dt < window_start]
        baseline_count = len(baseline_dts)
        num_windows = max(1, int(baseline_span.total_seconds() // window.total_seconds()))
        baseline_avg = baseline_count / num_windows
        if recent >= max(spike_min_abs, int(math.ceil(baseline_avg * spike_multiplier))):
            alerts["pics_anormaux"].append({
                "type": "zone",
                "label": z.get("name"),
                "recent": recent,
                "baseline": round(baseline_avg, 2),
                "window_min": spike_window_min,
            })

    return render_template(
        "admin/pilotage.html",
        zone_rows=zone_rows,
        zone_detail=zone_detail,
        gauges=gauges,
        alerts=alerts,
        settings=settings,
    )


@app.route("/admin/pilotage/map_data")
@role_required("admin")
def admin_pilotage_map_data():
    """Données JSON pour la carte Leaflet (centres + progression).

    Retourne une liste de centres avec coordonnées (lat/lng) et des métriques
    de progression dans la fenêtre de la campagne.
    """
    zone_id = (request.args.get("zone") or "").strip() or None

    settings = _get_settings()
    zones = _get_active_zones()
    regs_all = [r for r in _get_regs() if _is_real(r)]
    centers_map = _get_centers_map()

    start_dt, end_dt = _campaign_window(settings)
    regs_all = [r for r in regs_all if _in_window(r, start_dt, end_dt)]

    # Objectifs (par zone) pour calculer la progression
    objectives_map = _get_objectives_map()
    zone_targets = {}
    # La structure des objectifs est de la forme {"zones": {zone_id: {...}}, "users": {...}}
    data = objectives_map or {}
    zones_cfg = data.get("zones", {}) if isinstance(data, dict) else {}
    for _zid, obj in zones_cfg.items():
        try:
            t = int((obj or {}).get("target") or 0)
        except Exception:
            t = 0
        if t > 0:
            zone_targets[_zid] = t

    # Paiements: un dossier est "payé" si le payslip (agent + période) est au statut PAID
    def _parse_dt_iso(v):
        if not v:
            return None
        try:
            s = str(v).strip()
            if s.endswith("Z"):
                s = s[:-1] + "+00:00"
            return datetime.fromisoformat(s)
        except Exception:
            return None

    paid_reg_ids = set()
    try:
        payroll = _get_payroll()
    except Exception:
        payroll = []

    paid_slips_by_agent = {}
    for slip in payroll or []:
        if slip.get("type") != "PAYSLIP":
            continue
        if slip.get("status") != "PAID":
            continue
        agent_id = slip.get("agent_id")
        start_iso = slip.get("period_start")
        end_iso = slip.get("period_end")
        if not agent_id or not start_iso or not end_iso:
            continue
        paid_slips_by_agent.setdefault(agent_id, []).append((start_iso, end_iso))

    regs_by_agent = {}
    for r in regs_all:
        agent_id = r.get("created_by")
        rid = r.get("id")
        dt = _parse_dt_iso(r.get("created_at"))
        if not agent_id or not rid or not dt:
            continue
        regs_by_agent.setdefault(agent_id, []).append((dt, rid))

    for agent_id, slips in paid_slips_by_agent.items():
        regs_list = regs_by_agent.get(agent_id, [])
        if not regs_list:
            continue
        for start_iso, end_iso in slips:
            start_dt2 = _parse_dt_iso(start_iso)
            end_dt2 = _parse_dt_iso(end_iso)
            if not start_dt2 or not end_dt2:
                continue
            for dt, rid in regs_list:
                if start_dt2 <= dt < end_dt2:
                    paid_reg_ids.add(rid)

    zone_by_id = {z.get("id"): z for z in zones}

    def _safe_float(v):
        if v is None:
            return None
        try:
            return float(str(v).replace(",", "."))
        except Exception:
            return None

    def _centers_for_zone(zid: str):
        # centre config par zone, sinon fallback sur _default
        return centers_map.get(zid) or centers_map.get("_default") or []

    def _center_index(zid: str):
        """Index centres by normalized name and by id for a given zone."""
        by_norm = {}
        by_id = {}
        for c in _centers_for_zone(zid):
            cid = (str(c.get("id") or "").strip())
            name = (c.get("name") or c.get("centre_name") or "").strip()
            if cid:
                by_id[cid] = c
            if name:
                by_norm[_norm_cmp(name)] = c
        return by_id, by_norm

    out = []

    zone_ids = [zone_id] if zone_id else [z.get("id") for z in zones]
    for zid in zone_ids:
        if not zid:
            continue
        z = zone_by_id.get(zid) or {}
        zname = (z.get("name") or zid).strip()
        zregs = [r for r in regs_all if r.get("zone_id") == zid]

        cfg_by_id, cfg_by_norm = _center_index(zid)

        # Objectif et progression globale de la zone
        zone_target = zone_targets.get(zid)
        zone_approved = sum(1 for r in zregs if r.get("status") == STATUS_APPROVED)
        zone_total = len(zregs)

        # Regroupement des enregistrements par centre (normalisation + id)
        regs_by_norm = {}
        for r in zregs:
            pc = (r.get("polling_center") or "").strip()
            pcid = (str(r.get("polling_center_id") or "").strip())
            cfg_match = None
            if pcid and pcid in cfg_by_id:
                cfg_match = cfg_by_id.get(pcid)
            else:
                cfg_match = _match_center_from_value(_centers_for_zone(zid), pc)
            if cfg_match:
                key = _norm_cmp(cfg_match.get("name") or "")
            else:
                key = _norm_cmp((pc.split("/")[0]).strip())
            regs_by_norm.setdefault(key, []).append(r)

        # centres observés dans les données + ceux du référentiel
        entries = {}
        for c in _centers_for_zone(zid):
            name = (c.get("name") or c.get("centre_name") or "").strip()
            if name:
                entries[_norm_cmp(name)] = {"name": name, "cfg": c}
        for r in zregs:
            pc = (r.get("polling_center") or "").strip()
            if not pc:
                continue
            cfg_match = _match_center_from_value(_centers_for_zone(zid), pc)
            disp = (cfg_match.get("name") if cfg_match else (pc.split("/")[0]).strip())
            nkey = _norm_cmp(disp)
            if nkey and nkey not in entries:
                entries[nkey] = {"name": disp, "cfg": {}}

        for nkey, entry in sorted(entries.items(), key=lambda kv: (kv[1].get("name") or "").lower()):
            cname = entry.get("name") or ""
            cfg = entry.get("cfg") or {}
            lat = _safe_float(cfg.get("lat"))
            lng = _safe_float(cfg.get("lng"))

            cregs = regs_by_norm.get(nkey, [])
            # Dossiers du centre (tous statuts, hors brouillons)
            total_count = len(cregs)
            verified_count = sum(1 for r in cregs if r.get("status") in (STATUS_VERIFIED, STATUS_APPROVED))
            approved_count = sum(1 for r in cregs if r.get("status") == STATUS_APPROVED)
            paid_count = sum(1 for r in cregs if (r.get("id") in paid_reg_ids))

            # Progression affichée :
            # vision globale = total approuvés de la zone / objectif de la zone
            if zone_target:
                progress_pct = int(round((zone_approved / zone_target) * 100)) if zone_target else 0
            else:
                # à défaut d'objectif, progression = part des dossiers approuvés sur le total de la zone
                progress_pct = int(round((zone_approved / zone_total) * 100)) if zone_total else 0
            progress_pct = max(0, min(100, progress_pct))


            stats = {
                # Total = dossiers (tous statuts) de la zone
                "total": zone_total,
                # Approuvés = dossiers approuvés de la zone (tous centres)
                "pending": sum(1 for r in zregs if r.get("status") == STATUS_PENDING),
                "corriger": sum(1 for r in zregs if r.get("status") == STATUS_NEEDS_CORRECTION),
                "verifies": sum(1 for r in zregs if r.get("status") == STATUS_VERIFIED),
                "approuves": zone_approved,
                "rejetes": sum(1 for r in zregs if r.get("status") == STATUS_REJECTED),
            }

            # Bureaux (liste issue du référentiel + ceux vus en data)
            bureaux_cfg = (cfg.get("bureaux") or [])
            bureau_names = []
            for b in bureaux_cfg:
                if isinstance(b, dict):
                    bn = b.get("name") or b.get("id")
                else:
                    bn = str(b) if b is not None else ""
                bn = (bn or "").strip()
                if bn:
                    bureau_names.append(bn)
            seen_b = sorted(set([r.get("polling_station") for r in cregs if r.get("polling_station")]))
            for bn in seen_b:
                if bn and bn not in bureau_names:
                    bureau_names.append(bn)
            bureau_names = [bn for bn in bureau_names if bn]
            bureau_names.sort(key=lambda s: s.lower())

            bureaux = []
            for bn in bureau_names:
                bregs = [r for r in cregs if r.get("polling_station") == bn]
                bureaux.append({
                    "name": bn,
                    "total": len(bregs),
                    "pending": sum(1 for r in bregs if r.get("status") == STATUS_PENDING),
                    "corriger": sum(1 for r in bregs if r.get("status") == STATUS_NEEDS_CORRECTION),
                    "verifies": sum(1 for r in bregs if r.get("status") == STATUS_VERIFIED),
                    "approuves": sum(1 for r in bregs if r.get("status") == STATUS_APPROVED),
                    "rejetes": sum(1 for r in bregs if r.get("status") == STATUS_REJECTED),
                })

            out.append({
                "zone_id": zid,
                "zone_name": zname,
                "center_id": cfg.get("id"),
                "center_name": cname,
                "office_name": (cfg.get("office_name") or cfg.get("office") or "").strip(),
                "lat": lat,
                "lng": lng,
                "total_count": zone_total,
                "verified_count": verified_count,
                "paid_count": paid_count,
                "approved_count": int(stats.get("approuves", 0)),
                "progress_pct": progress_pct,
                "stats": stats,
                "bureaux": bureaux,
            })

    return jsonify({
        "campaign": {
            "start": start_dt.isoformat() if start_dt else None,
            "end": end_dt.isoformat() if end_dt else None,
        },
        "centers": out,
    })


@app.route("/admin/users", methods=["GET", "POST"])
@role_required("admin")
def admin_users():
    users = _get_users()
    zones = _get_active_zones()

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "create").strip().lower()

        # Création d'un utilisateur
        if action == "create":
            username = (request.form.get("username") or "").strip()
            full_name = (request.form.get("full_name") or "").strip()
            role = (request.form.get("role") or "").strip()
            zone_id = (request.form.get("zone_id") or "").strip() or None
            supervisor_id = (request.form.get("supervisor_id") or "").strip() or None
            password = (request.form.get("password") or "").strip()

            if not (username and full_name and role and password):
                flash("Champs requis manquants.", "warning")
                return redirect(url_for("admin_users"))

            if any(u.get("username") == username for u in users):
                flash("Ce nom d'utilisateur existe déjà.", "danger")
                return redirect(url_for("admin_users"))



            if role == "agent":
                if not zone_id:
                    flash("Un agent doit avoir une zone.", "warning")
                    return redirect(url_for("admin_users"))
                if not supervisor_id:
                    flash("Un agent doit être rattaché à un superviseur.", "warning")
                    return redirect(url_for("admin_users"))

                sup = next((x for x in users if x.get("id") == supervisor_id and x.get("role") == "supervisor"), None)
                if not sup:
                    flash("Superviseur invalide.", "warning")
                    return redirect(url_for("admin_users"))
                if (sup.get("zone_id") or None) != zone_id:
                    flash("Le superviseur sélectionné doit appartenir à la même zone que l'agent.", "warning")
                    return redirect(url_for("admin_users"))

            rec = {
                "id": str(uuid.uuid4()),
                "username": username,
                "full_name": full_name,
                "role": role,
                "zone_id": zone_id,
                "supervisor_id": supervisor_id,
                "password_hash": generate_password_hash(password),
                "created_at": _now_iso(),
                "is_active": True,
            }
            users.append(rec)
            _save_users(users)
            _audit("user.create", current_user()["id"], "user", rec["id"], {"role": role, "username": username})
            flash("Utilisateur ajouté.", "success")
            return redirect(url_for("admin_users"))

        flash("Action inconnue.", "warning")
        return redirect(url_for("admin_users"))

    supervisors = [u for u in users if u.get("role") == "supervisor"]
    zones_map = {z.get("id"): z for z in zones}
    locked_ids = _get_locked_user_ids(users)
    return render_template(
        "admin/users.html",
        users=users,
        zones=zones,
        zones_map=zones_map,
        supervisors=supervisors,
        locked_user_ids=locked_ids,
        zone_name=_zone_name,
    )


@app.route("/admin/users/<user_id>/edit", methods=["GET", "POST"])
@role_required("admin")
def admin_user_edit(user_id: str):
    users = _get_users()
    user = next((u for u in users if u.get("id") == user_id), None)
    if not user:
        flash("Utilisateur introuvable.", "danger")
        return redirect(url_for("admin_users"))

    zones = _get_active_zones()
    supervisors = [u for u in users if u.get("role") == "supervisor"]

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        full_name = (request.form.get("full_name") or "").strip()
        role = (request.form.get("role") or "").strip()
        zone_id = (request.form.get("zone_id") or "").strip() or None
        supervisor_id = (request.form.get("supervisor_id") or "").strip() or None

        if not (full_name and role):
            flash("Champs requis manquants.", "warning")
            return redirect(url_for("admin_user_edit", user_id=user_id))



        if role == "agent":
            if not zone_id:
                flash("Un agent doit avoir une zone.", "warning")
                return redirect(url_for("admin_user_edit", user_id=user_id))
            if not supervisor_id:
                flash("Un agent doit être rattaché à un superviseur.", "warning")
                return redirect(url_for("admin_user_edit", user_id=user_id))

            sup = next((x for x in users if x.get("id") == supervisor_id and x.get("role") == "supervisor"), None)
            if not sup:
                flash("Superviseur invalide.", "warning")
                return redirect(url_for("admin_user_edit", user_id=user_id))
            if (sup.get("zone_id") or None) != zone_id:
                flash("Le superviseur sélectionné doit appartenir à la même zone que l'agent.", "warning")
                return redirect(url_for("admin_user_edit", user_id=user_id))

        user["full_name"] = full_name
        user["role"] = role
        user["zone_id"] = zone_id
        user["supervisor_id"] = supervisor_id

        _save_users(users)
        _audit(
            "user.update",
            current_user()["id"],
            "user",
            user["id"],
            {"role": role, "username": user.get("username")},
        )
        flash("Utilisateur modifié.", "success")
        return redirect(url_for("admin_users"))

    return render_template(
        "admin/user_edit.html",
        user=user,
        zones=zones,
        supervisors=supervisors,
        zone_name=_zone_name,
    )


@app.route("/admin/users/<user_id>/delete", methods=["POST"])
@role_required("admin")
def admin_user_delete(user_id: str):
    if not _csrf_validate():
        abort(400)

    users = _get_users()
    user = next((u for u in users if u.get("id") == user_id), None)
    if not user:
        flash("Utilisateur introuvable.", "danger")
        return redirect(url_for("admin_users"))

    if user.get("username") == "admin":
        flash("Le compte administrateur ne peut pas être supprimé.", "warning")
        return redirect(url_for("admin_users"))

    locked_ids = _get_locked_user_ids(users)
    if user_id in locked_ids:
        flash(
            "Impossible de supprimer cet utilisateur car il/elle a déjà des dossiers validés ou a validé des dossiers. "
            "Désactivez plutôt le compte.",
            "warning",
        )
        return redirect(url_for("admin_users"))

    users = [u for u in users if u.get("id") != user_id]
    _save_users(users)
    _audit(
        "user.delete",
        current_user()["id"],
        "user",
        user_id,
        {"username": user.get("username")},
    )
    flash("Utilisateur supprimé.", "success")
    return redirect(url_for("admin_users"))


@app.route("/admin/users/<user_id>/toggle", methods=["POST"])
@role_required("admin")
def admin_user_toggle(user_id: str):
    if not _csrf_validate():
        abort(400)

    users = _get_users()
    for u in users:
        if u.get("id") == user_id:
            u["is_active"] = not bool(u.get("is_active", True))
            _save_users(users)
            _audit(
                "user.toggle_active",
                current_user()["id"],
                "user",
                user_id,
                {"is_active": u["is_active"]},
            )
            flash("Statut de l'utilisateur mis à jour.", "success")
            break
    else:
        flash("Utilisateur introuvable.", "danger")

    return redirect(url_for("admin_users"))


@app.route("/admin/users/<user_id>/reset_password", methods=["POST"])
@role_required("admin")
def admin_user_reset_password(user_id: str):
    if not _csrf_validate():
        abort(400)

    new_password = (request.form.get("new_password") or "").strip()
    if not new_password:
        flash("Mot de passe manquant.", "warning")
        return redirect(url_for("admin_users"))

    users = _get_users()
    for u in users:
        if u.get("id") == user_id:
            u["password_hash"] = generate_password_hash(new_password)
            _save_users(users)
            _audit(
                "user.reset_password",
                current_user()["id"],
                "user",
                user_id,
                {"username": u.get("username")},
            )
            flash("Mot de passe réinitialisé.", "success")
            break
    else:
        flash("Utilisateur introuvable.", "danger")

    return redirect(url_for("admin_users"))
@app.route("/admin/settings", methods=["GET", "POST"])
@role_required("admin")
def admin_settings():
    settings = _get_settings()
    zones = _get_zones()
    centers_map = _get_centers_map()
    pop_zone_id = (request.args.get("pop_zone") or "").strip()
    if not pop_zone_id and zones:
        pop_zone_id = zones[0].get("id")
    pop_centers = centers_map.get(pop_zone_id, []) if pop_zone_id else []

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "").strip()

        # Population électorale (par centre)
        if action == "update_center_pops":
            zone_id = (request.form.get("pop_zone_id") or "").strip()
            if not zone_id:
                flash("Veuillez choisir une zone.", "warning")
                return redirect(url_for("admin_settings"))

            users = _get_users()  # pour audit cohérent
            centers_map = _get_centers_map()
            zone_centers = centers_map.get(zone_id, [])

            updated = 0
            for c in zone_centers:
                cid = str(c.get("id") or "").strip()
                if not cid:
                    continue
                raw = (request.form.get(f"pop_{cid}") or "").strip()
                raw_clean = raw.replace(" ", "").replace("\u00A0", "")
                if raw_clean == "":
                    if "pop_elect" in c:
                        c.pop("pop_elect", None)
                        updated += 1
                    continue
                try:
                    val = int(float(raw_clean))
                except Exception:
                    val = 0
                if val <= 0:
                    if "pop_elect" in c:
                        c.pop("pop_elect", None)
                        updated += 1
                else:
                    if c.get("pop_elect") != val:
                        c["pop_elect"] = val
                        updated += 1

            centers_map[zone_id] = zone_centers
            _save_centers_map(centers_map)
            _audit(
                "centers.pop.update",
                current_user()["id"],
                "centers",
                zone_id,
                {"updated": updated, "zone_id": zone_id},
            )
            flash("Populations électorales enregistrées.", "success")
            return redirect(url_for("admin_settings", pop_zone=zone_id))

        # Existing
        try:
            settings["pay_rate"] = float((request.form.get("pay_rate") or "0").replace(",", "."))
        except Exception:
            settings["pay_rate"] = 0.0

        # Prime fixe par période (14 jours)
        try:
            settings["pay_fixed_bonus"] = int((request.form.get("pay_fixed_bonus") or "0").strip())
            if settings["pay_fixed_bonus"] < 0:
                settings["pay_fixed_bonus"] = 0
        except Exception:
            settings["pay_fixed_bonus"] = int(settings.get("pay_fixed_bonus", PAY_FIXED_BONUS_CFA) or PAY_FIXED_BONUS_CFA)

        settings["double_approval"] = True if (request.form.get("double_approval") or "").strip().lower() in ("1","on","true","yes") else False

        # Pilotage (supervision terrain)
        settings["campaign_start_date"] = (request.form.get("campaign_start_date") or "").strip()
        settings["campaign_end_date"] = (request.form.get("campaign_end_date") or "").strip()

        def _int_field(name: str, default: int) -> int:
            try:
                return int((request.form.get(name) or str(default)).strip())
            except Exception:
                return default

        def _float_field(name: str, default: float) -> float:
            try:
                return float((request.form.get(name) or str(default)).replace(",", ".").strip())
            except Exception:
                return default

        settings["pilotage_inactivity_hours"] = max(1, _int_field("pilotage_inactivity_hours", int(settings.get("pilotage_inactivity_hours", 6) or 6)))
        settings["pilotage_spike_window_minutes"] = max(5, _int_field("pilotage_spike_window_minutes", int(settings.get("pilotage_spike_window_minutes", 60) or 60)))
        settings["pilotage_spike_multiplier"] = max(1.0, _float_field("pilotage_spike_multiplier", float(settings.get("pilotage_spike_multiplier", 3) or 3)))
        settings["pilotage_spike_min_abs"] = max(1, _int_field("pilotage_spike_min_abs", int(settings.get("pilotage_spike_min_abs", 10) or 10)))
        settings["pilotage_behind_slack_pct"] = max(0, _int_field("pilotage_behind_slack_pct", int(settings.get("pilotage_behind_slack_pct", 10) or 10)))

        _save_settings(settings)
        _audit(
            "settings.update",
            current_user()["id"],
            "settings",
            "settings",
            {
                "pay_rate": settings.get("pay_rate"),
                "pay_fixed_bonus": settings.get("pay_fixed_bonus"),
                "double_approval": settings.get("double_approval"),
                "campaign_start_date": settings.get("campaign_start_date"),
                "campaign_end_date": settings.get("campaign_end_date"),
                "pilotage_inactivity_hours": settings.get("pilotage_inactivity_hours"),
                "pilotage_spike_window_minutes": settings.get("pilotage_spike_window_minutes"),
                "pilotage_spike_multiplier": settings.get("pilotage_spike_multiplier"),
                "pilotage_spike_min_abs": settings.get("pilotage_spike_min_abs"),
                "pilotage_behind_slack_pct": settings.get("pilotage_behind_slack_pct"),
            },
        )
        flash("Paramètres enregistrés.", "success")
        return redirect(url_for("admin_settings"))

    return render_template("admin/settings.html", settings=settings, zones=zones, pop_zone_id=pop_zone_id, pop_centers=pop_centers)
@app.route("/admin/reset-data", methods=["POST"])
@role_required("admin")
def admin_reset_data():
    """Réinitialisation contrôlée des données (avec sauvegarde automatique).

    Permet de remettre à zéro :
    - Liste des recensés (registrations.json)
    - Paiements (payroll.json)
    - Comptes agents recenseurs
    - Comptes superviseurs

    Les admins sont conservés.
    """
    if not _csrf_validate():
        abort(400)

    confirm = (request.form.get("confirm_text") or "").strip().upper()
    if confirm != "RESET":
        flash("Pour confirmer la réinitialisation, tapez RESET.", "danger")
        return redirect(url_for("admin_settings"))

    reset_registrations = request.form.get("reset_registrations") == "1"
    reset_payroll = request.form.get("reset_payroll") == "1"
    reset_agents = request.form.get("reset_agents") == "1"
    reset_supervisors = request.form.get("reset_supervisors") == "1"

    if not any([reset_registrations, reset_payroll, reset_agents, reset_supervisors]):
        flash("Sélectionnez au moins un élément à réinitialiser.", "warning")
        return redirect(url_for("admin_settings"))

    # Sauvegarde automatique avant toute réinitialisation
    os.makedirs(BACKUPS_DIR, exist_ok=True)
    ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    backup_zip = os.path.join(BACKUPS_DIR, f"backup_reset_{ts}.zip")
    with zipfile.ZipFile(backup_zip, "w", zipfile.ZIP_DEFLATED) as z:
        files = [USERS_FILE, REG_FILE, SETTINGS_FILE, PAYROLL_FILE, APPROVALS_QUEUE_FILE, CENTERS_FILE, ZONES_FILE]
        if _db_enabled():
            # Export from DB (source of truth)
            for p in files:
                key = os.path.basename(p)
                payload = _load_json(p, None)
                if payload is None:
                    continue
                z.writestr(key, json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            for p in files:
                if os.path.exists(p):
                    z.write(p, arcname=os.path.basename(p))

    # Reset recensés (+ file d'approbations)
    if reset_registrations:
        _save_json(REG_FILE, [])
        _save_json(APPROVALS_QUEUE_FILE, [])

    # Reset paiements
    if reset_payroll:
        _save_json(PAYROLL_FILE, [])

    # Reset comptes utilisateurs (agents / superviseurs)
    if reset_agents or reset_supervisors:
        users = _load_json(USERS_FILE, [])
        new_users = []
        for u in users:
            role = (u.get("role") or "").strip().lower()
            if role == "admin":
                new_users.append(u)
                continue
            if role == "agent" and reset_agents:
                continue
            if role == "supervisor" and reset_supervisors:
                continue
            new_users.append(u)

        # Sécurité : au moins 1 admin doit rester.
        if not any((u.get("role") or "").strip().lower() == "admin" for u in new_users):
            flash("Réinitialisation annulée : aucun compte admin ne resterait.", "danger")
            return redirect(url_for("admin_settings"))

        _save_json(USERS_FILE, new_users)

    flash(f"Réinitialisation effectuée. Sauvegarde créée : {os.path.basename(backup_zip)}", "success")
    return redirect(url_for("admin_settings"))


# --- Centers & bureaux ---
@app.route("/admin/centers", methods=["GET", "POST"])
@role_required("admin")
def admin_centers():
    zones = _get_active_zones()
    centers_map = _get_centers_map()

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)
        action = (request.form.get("action") or "").strip()
        zone_id = (request.form.get("zone_id") or "").strip()
        if not zone_id:
            flash("Zone requise.", "warning")
            return redirect(url_for("admin_centers"))

        centers_map.setdefault(zone_id, [])

        if action == "add_center":
            name = (request.form.get("center_name") or "").strip()
            if not name:
                flash("Nom du centre requis.", "warning")
                return redirect(url_for("admin_centers"))
            centers_map[zone_id].append({
                "id": str(uuid.uuid4()),
                "name": name,
                "bureaux": [],
                # Coordonnées GPS (optionnelles) pour l'affichage sur carte
                "lat": None,
                "lng": None,
            })
            _save_centers_map(centers_map)
            _audit("center.create", current_user()["id"], "center", zone_id, {"name": name})
            flash("Centre ajouté.", "success")
            return redirect(url_for("admin_centers", zone_id=zone_id))

        if action == "update_center":
            center_id = (request.form.get("center_id") or "").strip()
            name = (request.form.get("center_name") or "").strip()
            lat_raw = (request.form.get("lat") or "").strip()
            lng_raw = (request.form.get("lng") or "").strip()

            def _to_float(v):
                if v is None:
                    return None
                v = str(v).strip()
                if not v:
                    return None
                # allow comma
                v = v.replace(",", ".")
                return float(v)

            lat = None
            lng = None
            try:
                lat = _to_float(lat_raw)
                lng = _to_float(lng_raw)
            except Exception:
                flash("Latitude/Longitude invalides. Exemple : 5.3278 / -3.9861", "warning")
                return redirect(url_for("admin_centers", zone_id=zone_id))

            updated = False
            for c in centers_map.get(zone_id, []):
                if c.get("id") == center_id:
                    if name:
                        c["name"] = name
                    c["lat"] = lat
                    c["lng"] = lng
                    updated = True
                    break

            if not updated:
                flash("Centre introuvable.", "danger")
                return redirect(url_for("admin_centers", zone_id=zone_id))

            _save_centers_map(centers_map)
            _audit(
                "center.update",
                current_user()["id"],
                "center",
                center_id,
                {"name": name, "lat": lat, "lng": lng},
            )
            flash("Centre mis à jour.", "success")
            return redirect(url_for("admin_centers", zone_id=zone_id))

        if action == "add_station":
            center_id = (request.form.get("center_id") or "").strip()
            station = (request.form.get("station") or "").strip()
            if not (center_id and station):
                flash("Centre et bureau requis.", "warning")
                return redirect(url_for("admin_centers", zone_id=zone_id))
            for c in centers_map.get(zone_id, []):
                if c.get("id") == center_id:
                    if station not in c.get("bureaux", []):
                        c.setdefault("bureaux", []).append(station)
                        c["bureaux"] = sorted(list({x for x in c["bureaux"] if x}))
                        _save_centers_map(centers_map)
                        _audit("station.create", current_user()["id"], "center", center_id, {"station": station})
                        flash("Bureau ajouté.", "success")
                    return redirect(url_for("admin_centers", zone_id=zone_id))
            flash("Centre introuvable.", "danger")
            return redirect(url_for("admin_centers", zone_id=zone_id))

        if action == "delete_center":
            center_id = (request.form.get("center_id") or "").strip()
            centers_map[zone_id] = [c for c in centers_map.get(zone_id, []) if c.get("id") != center_id]
            _save_centers_map(centers_map)
            _audit("center.delete", current_user()["id"], "center", center_id, {})
            flash("Centre supprimé.", "success")
            return redirect(url_for("admin_centers", zone_id=zone_id))

        if action == "delete_station":
            center_id = (request.form.get("center_id") or "").strip()
            station = (request.form.get("station") or "").strip()
            for c in centers_map.get(zone_id, []):
                if c.get("id") == center_id:
                    c["bureaux"] = [x for x in c.get("bureaux", []) if x != station]
                    _save_centers_map(centers_map)
                    _audit("station.delete", current_user()["id"], "center", center_id, {"station": station})
                    flash("Bureau supprimé.", "success")
                    return redirect(url_for("admin_centers", zone_id=zone_id))
            flash("Centre introuvable.", "danger")
            return redirect(url_for("admin_centers", zone_id=zone_id))

        if action == "update_center_coords":
            center_id = (request.form.get("center_id") or "").strip()
            lat_raw = (request.form.get("lat") or "").strip()
            lng_raw = (request.form.get("lng") or "").strip()

            def _to_float(v: str):
                if v is None:
                    return None
                v = v.strip()
                if not v:
                    return None
                # accepte virgule
                v = v.replace(",", ".")
                return float(v)

            try:
                lat = _to_float(lat_raw)
                lng = _to_float(lng_raw)
            except Exception:
                flash("Coordonnées invalides (lat/lng doivent être numériques).", "danger")
                return redirect(url_for("admin_centers", zone_id=zone_id))

            found = False
            for c in centers_map.get(zone_id, []):
                if c.get("id") == center_id:
                    c["lat"] = lat
                    c["lng"] = lng
                    found = True
                    break

            if not found:
                flash("Centre introuvable.", "danger")
                return redirect(url_for("admin_centers", zone_id=zone_id))

            _save_centers_map(centers_map)
            _audit("center.coords", current_user()["id"], "center", center_id, {"lat": lat, "lng": lng})
            flash("Coordonnées enregistrées.", "success")
            return redirect(url_for("admin_centers", zone_id=zone_id))

    selected_zone_id = (request.args.get("zone_id") or "").strip() or (zones[0]["id"] if zones else "")
    selected_centers = centers_map.get(selected_zone_id, [])

    # Liste des recensés de la zone sélectionnée.
    # Exigence : quand on choisit une zone, on doit voir *tous* les dossiers de la zone.
    # On ne filtre donc pas par statut ici (y compris les brouillons si présents).
    regs_all = _get_regs()
    regs_zone = [r for r in regs_all if r.get("zone_id") == selected_zone_id]
    regs_zone = sorted(regs_zone, key=lambda r: (r.get("created_at") or ""), reverse=True)
    regs_preview = regs_zone

    # Décompte (zone sélectionnée)
    zone_centers_count = len(selected_centers)
    zone_bureaux_count = 0
    for c in selected_centers:
        b = c.get("bureaux") or c.get("bureaus") or c.get("offices") or c.get("polling_stations")
        if isinstance(b, list):
            zone_bureaux_count += len(b)
        elif isinstance(b, int):
            zone_bureaux_count += b
        else:
            n = c.get("bureaux_count") or c.get("nb_bureaux") or c.get("count_bureaux")
            if isinstance(n, int):
                zone_bureaux_count += n


    # Population électorale totale par zone (somme des populations des centres)
    zone_population_totals = {}
    try:
        for zid, clist in centers_map.items():
            for c in (clist or []):
                pop_val = (
                    c.get('pop_elect')
                    or c.get('population_electorale')
                    or c.get('population')
                    or c.get('electoral_population')
                    or 0
                )
                try:
                    pop_int = int(pop_val)
                except Exception:
                    pop_int = 0
                zone_population_totals[zid] = zone_population_totals.get(zid, 0) + pop_int
    except Exception:
        zone_population_totals = {}

    return render_template(
        "admin/centers.html",
        zones=zones,
        zone_population_totals=zone_population_totals,
        # Template expects current_zone_id (used to render the selected zone and
        # the zone-specific sections). Keep selected_zone_id as well for
        # backward compatibility.
        current_zone_id=selected_zone_id,
        selected_zone_id=selected_zone_id,
        centers=selected_centers,
        zone_centers_count=zone_centers_count,
        zone_bureaux_count=zone_bureaux_count,
        zone_name=_zone_name,
        regs_preview=regs_preview,
        regs_total=len(regs_zone),
        find_user=_find_user,
        format_date=_format_date,
    )


# --- Centers: set coords (API) ---
@app.route("/admin/centers/by_zone")
@role_required("admin")
def admin_centers_by_zone():
    zone_id = str(request.args.get("zone") or "").strip()
    centers_map = _get_centers_map()

    # normalize to dict
    if isinstance(centers_map, list):
        centers_map = {"_default": centers_map}
    if not isinstance(centers_map, dict):
        centers_map = {"_default": []}

    centers = centers_map.get(zone_id) or centers_map.get("_default") or []

    out = []
    for c in centers:
        name = (c.get("name") or c.get("centre_name") or "").strip()
        if not name:
            continue
        cid = str(c.get("id") or c.get("centre_id") or name)
        out.append({"id": cid, "name": name, "lat": c.get("lat"), "lng": c.get("lng")})

    out.sort(key=lambda x: x["name"])
    return jsonify(out)

@app.route("/admin/centers/set_coords", methods=["POST"])
@role_required("admin")
def admin_centers_set_coords():
    payload = request.get_json(silent=True) or {}
    zone_id = str(payload.get("zone_id") or "").strip()
    center_id = str(payload.get("center_id") or "").strip()
    center_name = str(payload.get("center_name") or "").strip()
    lat = payload.get("lat")
    lng = payload.get("lng")

    if not zone_id or not center_id or lat is None or lng is None:
        return jsonify({"ok": False, "error": "missing"}), 400

    try:
        lat = float(lat)
        lng = float(lng)
    except Exception:
        return jsonify({"ok": False, "error": "invalid_coords"}), 400

    centers_map = _get_centers_map()
    # normalize to dict
    if isinstance(centers_map, list):
        centers_map = {"_default": centers_map}
    if not isinstance(centers_map, dict):
        centers_map = {"_default": []}

    # pick key to update: prefer explicit zone list if present; otherwise update _default
    key = zone_id if zone_id in centers_map else ("_default" if "_default" in centers_map else zone_id)
    centers = centers_map.get(key)
    if not isinstance(centers, list):
        centers = []
        centers_map[key] = centers

    target = None
    for c in centers:
        cid = str(c.get("id") or c.get("centre_id") or "").strip()
        cname = str(c.get("name") or c.get("centre_name") or "").strip()
        if cid == center_id or cname == center_id:
            target = c
            break

    if target is None:
        # create record in a compatible shape
        uses_centre_keys = any(isinstance(x, dict) and ("centre_id" in x or "centre_name" in x) for x in centers)
        if uses_centre_keys or ("_default" in centers_map):
            target = {
                "centre_id": center_id,
                "centre_name": center_name or center_id,
                "bureaux": [],
            }
        else:
            target = {
                "id": center_id,
                "name": center_name or center_id,
            }
        centers.append(target)

    # update coords
    target["lat"] = lat
    target["lng"] = lng

    # keep name consistent if provided
    if center_name:
        if "centre_id" in target or "centre_name" in target:
            target["centre_name"] = center_name
        else:
            target["name"] = center_name

    _save_centers_map(centers_map)

    # Audit
    _audit(
        "CENTER_COORDS_UPDATE",
        {
            "zone_id": zone_id,
            "center_id": center_id,
            "center_name": center_name or (target.get("name") or target.get("centre_name") or ""),
            "lat": lat,
            "lng": lng,
            "store_key": key,
        },
        target_type="center",
        target_id=center_id,
    )

    return jsonify({"ok": True})

@app.route("/admin/objectives", methods=["GET", "POST"])
@role_required("admin")
def admin_objectives():
    zones = _get_active_zones()
    regs = _get_regs()
    users = _get_users()

    settings = _get_settings()
    centers_map = _get_centers_map()

    # Taux de participation moyen (en %) — utilisé pour estimer l’objectif par zone
    try:
        avg_turnout_pct = float((settings.get("avg_turnout_pct", 70) or 70))
    except Exception:
        avg_turnout_pct = 70.0

    # Population électorale totale par zone (somme des populations des centres)
    zone_population_totals = {}
    try:
        for zid, clist in (centers_map or {}).items():
            total_pop = 0
            for c in (clist or []):
                pop_val = (
                    c.get("pop_elect")
                    or c.get("population_electorale")
                    or c.get("population")
                    or c.get("electoral_population")
                    or 0
                )
                try:
                    total_pop += int(pop_val)
                except Exception:
                    pass
            zone_population_totals[str(zid)] = total_pop
    except Exception:
        zone_population_totals = {}


    obj = _get_objectives_map()
    zone_objectives = obj.get("zones", {}) if isinstance(obj, dict) else {}
    user_objectives = obj.get("users", {}) if isinstance(obj, dict) else {}

    # Only agents & supervisors for per-user objectives
    target_users = [u for u in users if u.get("role") in ("agent", "supervisor")]

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        # Paramètre: taux de participation moyen (en %)
        try:
            avg_turnout_pct = float((request.form.get("avg_turnout_pct") or str(avg_turnout_pct)).replace(",", ".").strip())
        except Exception:
            pass
        if avg_turnout_pct < 0:
            avg_turnout_pct = 0.0
        if avg_turnout_pct > 100:
            avg_turnout_pct = 100.0
        settings["avg_turnout_pct"] = avg_turnout_pct

        action = (request.form.get("action") or "").strip().lower()

        # zones
        for z in zones:
            zid = str(z.get("id"))

            # Pourcentage visé dans la zone (en %)
            desired_raw = (request.form.get(f"desired_{zid}") or "").strip().replace(",", ".")
            try:
                desired_pct = float(desired_raw) if desired_raw else float((zone_objectives.get(zid) or {}).get("desired_pct", 50) or 50)
            except Exception:
                desired_pct = float((zone_objectives.get(zid) or {}).get("desired_pct", 50) or 50)

            if desired_pct < 0:
                desired_pct = 0.0
            if desired_pct > 100:
                desired_pct = 100.0

            # Objectif (manuel ou auto)
            if action == "autofill":
                pop = int(zone_population_totals.get(zid, 0) or 0)
                target = int(round(pop * (avg_turnout_pct / 100.0) * (desired_pct / 100.0))) if pop else 0
            else:
                val = (request.form.get(f"target_{zid}") or "").strip()
                try:
                    target = int(val) if val else 0
                except Exception:
                    target = 0

            zone_objectives[zid] = {"target": max(0, int(target)), "desired_pct": desired_pct}

        _save_settings(settings)

        # users
        for u in target_users:
            uid = u.get("id")
            val = (request.form.get(f"utarget_{uid}") or "").strip()
            try:
                t = int(val) if val else 0
            except Exception:
                t = 0
            user_objectives[str(uid)] = {"target": max(0, t)}

        _save_objectives_map({"zones": zone_objectives, "users": user_objectives})
        # Audit (ne doit jamais casser l'enregistrement)
        try:
            _audit(
                "objectives.save",
                current_user()["id"],
                "objectives",
                "bulk",
                {"zones": len(zone_objectives), "users": len(user_objectives)},
            )
        except Exception:
            pass
        flash("Objectifs enregistrés.", "success")
        return redirect(url_for("admin_objectives"))

    # Zone table
    rows = []
    for z in zones:
        zid = z.get("id")
        target = int((zone_objectives.get(str(zid)) or {}).get("target", 0) or 0)
        total = sum(1 for r in regs if r.get("zone_id") == zid and r.get("status") != STATUS_DRAFT)
        pct = int((total / target) * 100) if target else 0
        pop = int(zone_population_totals.get(str(zid), 0) or 0)
        desired_pct = float((zone_objectives.get(str(zid)) or {}).get("desired_pct", 50) or 50)
        suggested = int(round(pop * (avg_turnout_pct / 100.0) * (desired_pct / 100.0))) if pop else 0
        rows.append({"zone": z, "target": target, "total": total, "pct": pct, "pop": pop, "desired_pct": desired_pct, "suggested": suggested})

    # User table (gauge on non-draft dossiers)
    user_rows = []
    for u in target_users:
        uid = u.get("id")
        role = u.get("role")
        target = int((user_objectives.get(str(uid)) or {}).get("target", 0) or 0)
        if role == "agent":
            done = sum(1 for r in regs if r.get("created_by") == uid and r.get("status") != STATUS_DRAFT)
        else:
            done = sum(1 for r in regs if r.get("verified_by") == uid and r.get("status") in (STATUS_VERIFIED, STATUS_APPROVED))
        pct = int((done / target) * 100) if target else 0
        user_rows.append({"user": u, "role": role, "target": target, "done": done, "pct": pct})

    return render_template("admin/objectives.html", rows=rows, user_rows=user_rows, avg_turnout_pct=avg_turnout_pct)
@app.route("/admin/audit")
@role_required("admin")
def admin_audit():
    q = (request.args.get("q") or "").strip().lower()
    action = (request.args.get("action") or "").strip().lower()
    actor = (request.args.get("actor") or "").strip()

    log = _load_json(AUDIT_FILE, [])
    if not isinstance(log, list):
        log = []

    def _match(e: Dict[str, Any]) -> bool:
        if action and (e.get("action") or "").lower() != action:
            return False
        if actor and (e.get("actor_id") or "") != actor:
            return False
        if q:
            hay = " ".join([
                (e.get("action") or ""),
                (e.get("target_type") or ""),
                (e.get("target_id") or ""),
                json.dumps(e.get("details") or {}, ensure_ascii=False),
            ]).lower()
            return q in hay
        return True

    filtered = [e for e in log if isinstance(e, dict) and _match(e)]
    filtered = sorted(filtered, key=lambda x: x.get("at") or "", reverse=True)

    page = request.args.get("page", "1")
    pag = _paginate(filtered, int(page) if str(page).isdigit() else 1, 50)

    return render_template("admin/audit.html", events=pag["items"], pagination=pag, find_user=_find_user)


# --- Backup / restore ---
@app.route("/admin/backup")
@role_required("admin")
def admin_backup():
    """Create a ZIP backup of data/ + uploads/.

    If PostgreSQL is enabled, we export the DB KV store (jsonb) into the ZIP.
    """
    u = current_user()
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    name = f"backup_{ts}.zip"
    out_path = os.path.join(BACKUPS_DIR, name)

    with zipfile.ZipFile(out_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
        # data
        if _db_enabled():
            dump = _kv_dump_all()
            for key, data in dump.items():
                if not str(key).lower().endswith(".json"):
                    continue
                z.writestr(f"data/{key}", json.dumps(data, ensure_ascii=False, indent=2))
        else:
            for fn in os.listdir(DATA_DIR):
                if fn.lower().endswith(".json"):
                    z.write(os.path.join(DATA_DIR, fn), arcname=f"data/{fn}")

        # uploads
        for fn in os.listdir(UPLOADS_DIR):
            z.write(os.path.join(UPLOADS_DIR, fn), arcname=f"uploads/{fn}")

    _audit("backup.create", u["id"], "backup", name, {})
    return send_file(out_path, as_attachment=True, download_name=name)


@app.route("/admin/restore", methods=["GET", "POST"])
@role_required("admin")
def admin_restore():
    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        confirm = (request.form.get("confirm") or "").strip().upper()
        if confirm != "RESTORE":
            flash("Tape RESTORE pour confirmer.", "warning")
            return redirect(url_for("admin_restore"))

        f = request.files.get("backup_zip")
        if not f or not f.filename:
            flash("Fichier ZIP requis.", "warning")
            return redirect(url_for("admin_restore"))

        # Save uploaded zip temporarily
        tmp = os.path.join(BACKUPS_DIR, f"uploaded_{uuid.uuid4().hex}.zip")
        f.save(tmp)

        # Safety backup first (DB-aware)
        try:
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            safety_name = f"backup_before_restore_{ts}.zip"
            safety_path = os.path.join(BACKUPS_DIR, safety_name)
            with zipfile.ZipFile(safety_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
                if _db_enabled():
                    dump = _kv_dump_all()
                    for key, data in dump.items():
                        if str(key).lower().endswith(".json"):
                            z.writestr(f"data/{key}", json.dumps(data, ensure_ascii=False, indent=2))
                else:
                    for fn in os.listdir(DATA_DIR):
                        if fn.lower().endswith(".json"):
                            z.write(os.path.join(DATA_DIR, fn), arcname=f"data/{fn}")
                for fn in os.listdir(UPLOADS_DIR):
                    z.write(os.path.join(UPLOADS_DIR, fn), arcname=f"uploads/{fn}")
        except Exception:
            pass

        try:
            with zipfile.ZipFile(tmp, "r") as z:
                members = z.namelist()
                if not any(m.startswith("data/") and m.lower().endswith(".json") for m in members):
                    flash("ZIP invalide (dossier data/ manquant).", "danger")
                    return redirect(url_for("admin_restore"))

                # Extract to temp dir
                extract_dir = os.path.join(BACKUPS_DIR, f"restore_{uuid.uuid4().hex}")
                os.makedirs(extract_dir, exist_ok=True)
                z.extractall(extract_dir)

                data_src = os.path.join(extract_dir, "data")
                uploads_src = os.path.join(extract_dir, "uploads")

                # Restore JSON -> DB (if enabled) + disk
                if os.path.isdir(data_src):
                    for fn in os.listdir(data_src):
                        if not fn.lower().endswith(".json"):
                            continue
                        src = os.path.join(data_src, fn)
                        try:
                            with open(src, "r", encoding="utf-8") as rf:
                                payload = json.load(rf)
                        except Exception:
                            continue
                        _save_json(os.path.join(DATA_DIR, fn), payload)

                # Restore uploads as-is
                if os.path.isdir(uploads_src):
                    for fn in os.listdir(uploads_src):
                        shutil.copy2(os.path.join(uploads_src, fn), os.path.join(UPLOADS_DIR, fn))

            _audit("backup.restore", current_user()["id"], "backup", os.path.basename(tmp), {})
            flash("Restauration effectuée. Recharge la page.", "success")
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass

        return redirect(url_for("admin_dashboard"))

    return render_template("admin/restore.html")

# --- Approvals (double validation) ---
@app.route("/admin/approvals", methods=["GET", "POST"])
@role_required("admin")
def admin_approvals():
    settings = _get_settings()
    # Force: any supervisor-verified dossier must pass through admin approvals
    double_approval = True

    # Actions (approve / reject)
    # NOTE: l'UI envoie une liste de cases cochées: name="reg_ids".
    # On supporte aussi l'ancien mode (un seul id) via name="id".
    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        u = current_user()
        action = (request.form.get("action") or "").strip()
        reg_ids = [str(x).strip() for x in request.form.getlist("reg_ids") if str(x).strip()]
        if not reg_ids:
            single_id = (request.form.get("id") or "").strip()
            if single_id:
                reg_ids = [single_id]

        if not reg_ids:
            flash("Aucun dossier sélectionné.", "warning")
            return redirect(url_for("admin_approvals"))

        if action not in {"approve", "reject"}:
            flash("Action inconnue.", "danger")
            return redirect(url_for("admin_approvals"))

        regs = _get_regs()
        by_id = {str(x.get("id")): x for x in regs if isinstance(x, dict) and x.get("id")}

        now = _now_iso()
        admin_user = session.get("username") or "admin"

        approved = 0
        rejected = 0
        skipped = 0

        for reg_id in reg_ids:
            r = by_id.get(reg_id)
            before = _deepcopy_json(r) if r else None
            if not r:
                skipped += 1
                continue

            # Sécurité : si double validation est activée, on n'autorise l'admin
            # à traiter que les dossiers effectivement vérifiés par le superviseur.
            if double_approval and not _supervisor_mark(r):
                skipped += 1
                continue

            if action == "approve":
                r["status"] = STATUS_APPROVED
                r["admin_approved_by"] = admin_user
                r["admin_approved_at"] = now
                r["admin_approved"] = True
                r["needs_admin_approval"] = False
                r["approved_by"] = admin_user
                r["approved_at"] = now
                r.pop("admin_rejected_by", None)
                r.pop("admin_rejected_at", None)
                _dequeue_for_admin(reg_id)

                sc, miss = _compute_reliability_score(r)
                r["reliability_score"] = sc
                r["reliability_missing"] = miss
                _audit_reg_change("reg.admin_approve", u["id"], before, r, {"status": r.get("status"), "admin": admin_user})

                approved += 1
            else:  # reject
                r["status"] = STATUS_REJECTED
                r["admin_rejected_by"] = admin_user
                r["admin_rejected_at"] = now
                r["admin_approved"] = False
                r["needs_admin_approval"] = False
                r["rejected_by"] = admin_user
                r["rejected_at"] = now
                _dequeue_for_admin(reg_id)

                sc, miss = _compute_reliability_score(r)
                r["reliability_score"] = sc
                r["reliability_missing"] = miss
                _audit_reg_change("reg.admin_reject", u["id"], before, r, {"status": r.get("status"), "admin": admin_user})

                rejected += 1

        _save_regs(regs)

        if action == "approve":
            if approved:
                msg = f"{approved} dossier(s) approuvé(s)."
                if skipped:
                    msg += f" {skipped} ignoré(s)."
                flash(msg, "success")
            else:
                flash("Aucun dossier approuvé (vérifiez la sélection).", "warning")
        else:
            if rejected:
                msg = f"{rejected} dossier(s) rejeté(s)."
                if skipped:
                    msg += f" {skipped} ignoré(s)."
                flash(msg, "warning")
            else:
                flash("Aucun dossier rejeté (vérifiez la sélection).", "warning")

        return redirect(url_for("admin_approvals"))

    # GET: Build a robust pending list.
    regs = _get_regs()
    by_id = {r.get("id"): r for r in regs if r.get("id")}

    existing_queue = _get_approval_queue()
    queue_out: list[str] = []
    seen: set[str] = set()
    regs_changed = False

    def _ensure_needs_admin(rr: dict) -> None:
        nonlocal regs_changed
        if not _norm_bool(rr.get("needs_admin_approval")):
            rr["needs_admin_approval"] = True
            regs_changed = True

    # 1) keep relevant items already in queue
    for rid in existing_queue:
        if rid in seen:
            continue
        rr = by_id.get(rid)
        if not rr:
            continue
        st = _canon_status(rr.get("status"))
        if st == STATUS_PAID:
            continue
        if _admin_done(rr):
            continue
        if not _supervisor_mark(rr, st=st):
            continue
        if double_approval:
            _ensure_needs_admin(rr)
        if _norm_bool(rr.get("needs_admin_approval")):
            queue_out.append(rid)
            seen.add(rid)

    # 2) self-healing: add any verified dossier that must be in approvals
    if double_approval:
        for rr in regs:
            rid = rr.get("id")
            if not rid or rid in seen:
                continue
            st = _canon_status(rr.get("status"))
            if st == STATUS_PAID:
                continue
            if _admin_done(rr):
                continue
            if not _supervisor_mark(rr, st=st):
                continue
            _ensure_needs_admin(rr)
            queue_out.append(rid)
            seen.add(rid)

    # Persist queue + optional reg flag update
    if queue_out != existing_queue:
        # NOTE: Le fichier de file d'attente s'appelle APPROVALS_QUEUE_FILE.
        # Un ancien nom (APPROVAL_QUEUE_FILE) provoquait un NameError.
        _save_json(APPROVALS_QUEUE_FILE, queue_out)
    if regs_changed:
        _save_regs(regs)

    # Build view models (ordered by queue)
    pending_view = []
    for rid in queue_out:
        rr = by_id.get(rid)
        if not rr:
            continue
        pending_view.append(
            {
                "id": rr.get("id"),
                "nom": rr.get("nom"),
                "prenoms": rr.get("prenoms"),
                "zone": rr.get("zone"),
                "agent_username": rr.get("agent_username"),
                "created_at": rr.get("created_at"),
                "verified_by": rr.get("supervisor_verified_by"),
                "verified_at": rr.get("supervisor_verified_at"),
            }
        )

    return render_template(
        "admin/approvals.html",
        pending=pending_view,
        settings=settings,
    )


@app.route("/admin/registrations")
@role_required("admin")
def admin_registrations():
    zones = _get_active_zones()
    regs = _get_regs()

    zone_id = (request.args.get("zone_id") or "").strip()
    polling_center = (request.args.get("polling_center") or "").strip()
    status_filter = (request.args.get("status") or "").strip()
    q = (request.args.get("q") or "").strip().lower()

    def _match(r: Dict[str, Any]) -> bool:
        if zone_id and r.get("zone_id") != zone_id:
            return False
        if polling_center and (r.get("polling_center") or "") != polling_center:
            return False
        if status_filter and (r.get("status") or "") != status_filter:
            return False
        if q:
            hay = " ".join(
                [
                    (r.get("nom") or ""),
                    (r.get("prenoms") or ""),
                    (r.get("telephone") or ""),
                    (r.get("quartier") or ""),
                    (r.get("voter_number") or ""),
                    (r.get("polling_center") or ""),
                    (r.get("polling_station") or ""),
                ]
            ).lower()
            return q in hay
        return True

    filtered = [r for r in regs if _match(r)]
    filtered_sorted = sorted(filtered, key=lambda r: r.get("created_at") or "", reverse=True)

    per_page = 20
    try:
        page = int(request.args.get("page", "1"))
    except ValueError:
        page = 1
    if page < 1:
        page = 1

    total = len(filtered_sorted)
    pages = max(1, (total + per_page - 1) // per_page)
    if page > pages:
        page = pages

    start = (page - 1) * per_page
    regs_page = filtered_sorted[start : start + per_page]

    centers = sorted({(r.get("polling_center") or "").strip() for r in regs if (r.get("polling_center") or "").strip()})
    statuses = [STATUS_DRAFT, STATUS_PENDING, STATUS_NEEDS_CORRECTION, STATUS_VERIFIED, STATUS_APPROVED, STATUS_REJECTED]

    return render_template(
        "admin/registrations.html",
        regs=regs_page,
        zones=zones,
        centers=centers,
        statuses=statuses,
        selected_zone_id=zone_id,
        selected_center=polling_center,
        selected_status=status_filter,
        q=q,
        total=total,
        pagination={
            "page": page,
            "pages": pages,
            "total_pages": pages,
            "per_page": per_page,
            "total": total,
            "has_prev": page > 1,
            "has_next": page < pages,
        },
        zone_name=_zone_name,
        find_user=_find_user,
        format_date=_format_date,
    )

@app.route("/admin/registration/<reg_id>/history")
@role_required("admin")
def admin_registration_history(reg_id: str):
    regs = _get_regs()
    reg = next((r for r in regs if str(r.get("id")) == str(reg_id)), None)
    if not reg:
        abort(404)

    logs = _get_audit()
    hist = [e for e in logs if (e.get("target_type") == "registration" and str(e.get("target_id")) == str(reg_id))]
    hist = _inject_admin_decision_events(reg, hist)
    hist = sorted(hist, key=lambda e: e.get("at") or "", reverse=True)

    # enrich actor
    for e in hist:
        e["_actor"] = _find_user(e.get("actor_id")) or {"full_name": e.get("actor_id") or "?"}

    return render_template(
        "admin/registration_history.html",
        reg=reg,
        history=hist,
        zone_name=_zone_name,
        format_date=_format_date,
        find_user=_find_user,
    )



@app.route("/admin/registrations/pdf", methods=["GET"])
@role_required("admin")
def admin_registrations_pdf():
    regs = _get_regs()

    zone_id = (request.args.get("zone_id") or "").strip()
    polling_center = (request.args.get("polling_center") or "").strip()
    status_filter = (request.args.get("status") or "").strip()
    q = (request.args.get("q") or "").strip().lower()

    def _match(r: Dict[str, Any]) -> bool:
        if zone_id and r.get("zone_id") != zone_id:
            return False
        if polling_center and (r.get("polling_center") or "") != polling_center:
            return False
        if status_filter and (r.get("status") or "") != status_filter:
            return False
        if q:
            hay = " ".join(
                [
                    (r.get("nom") or ""),
                    (r.get("prenoms") or ""),
                    (r.get("telephone") or ""),
                    (r.get("quartier") or ""),
                    (r.get("voter_number") or ""),
                    (r.get("polling_center") or ""),
                    (r.get("polling_station") or ""),
                ]
            ).lower()
            return q in hay
        return True

    filtered = [r for r in regs if _match(r)]
    filtered_sorted = sorted(filtered, key=lambda r: r.get("created_at") or "", reverse=True)

    try:
        from reportlab.lib.pagesizes import A4, landscape
        from reportlab.lib.units import mm
        from reportlab.lib import colors
        from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
        from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
        from reportlab.pdfbase.pdfmetrics import stringWidth
    except ModuleNotFoundError:
        flash("Le module 'reportlab' n'est pas installé. Exécute: pip install -r requirements.txt", "danger")
        return redirect(
            url_for(
                "admin_registrations",
                zone_id=zone_id,
                polling_center=polling_center,
                status=status_filter,
                q=q,
            )
        )

    # --- helpers ---
    from datetime import datetime
    from xml.sax.saxutils import escape

    def _p(text: str, style: ParagraphStyle) -> Paragraph:
        return Paragraph(escape(text or ""), style)

    # --- document ---
    buf = io.BytesIO()
    doc = SimpleDocTemplate(
        buf,
        pagesize=landscape(A4),
        leftMargin=10 * mm,
        rightMargin=10 * mm,
        topMargin=12 * mm,
        bottomMargin=10 * mm,
        title="Personnes recensées",
    )

    styles = getSampleStyleSheet()

    title_style = ParagraphStyle(
        "pdf_title",
        parent=styles["Title"],
        fontName="Helvetica-Bold",
        fontSize=16,
        leading=18,
        spaceAfter=2 * mm,
        textColor=colors.HexColor("#0f172a"),
    )

    meta_style = ParagraphStyle(
        "pdf_meta",
        parent=styles["Normal"],
        fontName="Helvetica",
        fontSize=9,
        leading=11,
        textColor=colors.HexColor("#334155"),
    )

    cell_style = ParagraphStyle(
        "pdf_cell",
        parent=styles["Normal"],
        fontName="Helvetica",
        fontSize=8.3,
        leading=10,
        textColor=colors.HexColor("#111827"),
    )

    cell_small = ParagraphStyle(
        "pdf_cell_small",
        parent=cell_style,
        fontSize=8,
        leading=9.5,
    )

    header_style = ParagraphStyle(
        "pdf_header",
        parent=styles["Normal"],
        fontName="Helvetica-Bold",
        fontSize=9,
        leading=10.5,
        textColor=colors.white,
    )

    # Title
    title = "Personnes recensées"
    if zone_id:
        title += f" — {_zone_name(zone_id)}"
    if polling_center:
        title += f" — {polling_center}"
    if status_filter:
        title += f" — {status_filter}"

    elems = []
    elems.append(Paragraph(title, title_style))

    # Meta line (count + filters)
    generated_at = datetime.now().strftime("%Y-%m-%d %H:%M")
    meta_parts = [f"Total: <b>{len(filtered_sorted)}</b>", f"Généré le: {generated_at}"]
    if q:
        meta_parts.append(f"Recherche: <b>{escape(q)}</b>")
    meta = " &nbsp;&nbsp;|&nbsp;&nbsp; ".join(meta_parts)
    elems.append(Paragraph(meta, meta_style))
    elems.append(Spacer(1, 5 * mm))

    # --- table ---
    headers = [
        "Nom",
        "Prénoms",
        "Naissance",
        "Quartier",
        "Téléphone",
        "Statut",
        "N° Électeur",
        "Centre de vote",
        "Bureau",
        "Zone",
    ]

    data = [[_p(h, header_style) for h in headers]]

    for r in filtered_sorted:
        data.append(
            [
                _p(r.get("nom") or "", cell_style),
                _p(r.get("prenoms") or "", cell_style),
                _p(_format_date(r.get("dob") or ""), cell_small),
                _p(r.get("quartier") or "", cell_style),
                _p(r.get("telephone") or "", cell_small),
                _p((r.get("status") or "").replace("_", " "), cell_small),
                _p(r.get("voter_number") or "", cell_small),
                _p(r.get("polling_center") or "", cell_style),
                _p(r.get("polling_station") or "", cell_small),
                _p(_zone_name(r.get("zone_id")), cell_style),
            ]
        )

    # Force full-width table (prevents the "tiny table" effect when data is short)
    # Base column widths in mm, then scaled to doc.width.
    base_mm = [26, 32, 20, 28, 24, 20, 34, 52, 18, 26]
    base_pts = [w * mm for w in base_mm]
    scale = (doc.width / sum(base_pts)) if sum(base_pts) else 1
    col_widths = [w * scale for w in base_pts]

    table = Table(data, colWidths=col_widths, repeatRows=1)

    # Styling
    table.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#0f172a")),
                ("LINEBELOW", (0, 0), (-1, 0), 0.6, colors.HexColor("#0f172a")),
                ("GRID", (0, 0), (-1, -1), 0.25, colors.HexColor("#e5e7eb")),
                ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#f8fafc")]),
                ("VALIGN", (0, 0), (-1, -1), "TOP"),
                ("LEFTPADDING", (0, 0), (-1, -1), 4),
                ("RIGHTPADDING", (0, 0), (-1, -1), 4),
                ("TOPPADDING", (0, 0), (-1, 0), 6),
                ("BOTTOMPADDING", (0, 0), (-1, 0), 6),
                ("TOPPADDING", (0, 1), (-1, -1), 3.5),
                ("BOTTOMPADDING", (0, 1), (-1, -1), 3.5),
                # align some columns
                ("ALIGN", (2, 1), (2, -1), "CENTER"),
                ("ALIGN", (4, 1), (4, -1), "CENTER"),
                ("ALIGN", (5, 1), (6, -1), "CENTER"),
                ("ALIGN", (8, 1), (8, -1), "CENTER"),
            ]
        )
    )

    elems.append(table)

    # Footer with page number
    def _on_page(canvas, doc_):
        canvas.saveState()
        canvas.setFont("Helvetica", 8)
        canvas.setFillColor(colors.HexColor("#64748b"))
        canvas.drawString(doc_.leftMargin, 7 * mm, "Eureka — Liste des personnes recensées")
        canvas.drawRightString(doc_.pagesize[0] - doc_.rightMargin, 7 * mm, f"Page {canvas.getPageNumber()}")
        canvas.restoreState()

    doc.build(elems, onFirstPage=_on_page, onLaterPages=_on_page)
    buf.seek(0)

    fname = "personnes_recensees.pdf"
    return send_file(buf, as_attachment=True, download_name=fname, mimetype="application/pdf")



# --- Admin SMS ---
@app.route("/admin/sms", methods=["GET", "POST"])
@role_required("admin")
def admin_sms():
    u = current_user()
    _process_due_campaigns(u["id"])  # auto-run scheduled

    regs = _get_regs()
    zones = _get_active_zones()
    cfg = _get_sms_config()

    # Centers list for filters
    centers = sorted({(r.get("polling_center") or "").strip() for r in regs if (r.get("polling_center") or "").strip()})

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "").strip()

        if action == "save_config":
            cfg["mode"] = (request.form.get("mode") or "dry_run").strip()
            cfg["sender_id"] = (request.form.get("sender_id") or "").strip()
            http_cfg = cfg.get("http_json") or {}
            http_cfg["url"] = (request.form.get("http_url") or "").strip()
            http_cfg["token"] = (request.form.get("http_token") or "").strip()
            http_cfg["to_field"] = (request.form.get("to_field") or "to").strip()
            http_cfg["message_field"] = (request.form.get("message_field") or "message").strip()
            http_cfg["sender_field"] = (request.form.get("sender_field") or "sender").strip()
            cfg["http_json"] = http_cfg
            _save_sms_config(cfg)
            _audit("sms.config", u["id"], "sms", "config", {"mode": cfg.get("mode")})
            flash("Configuration SMS enregistrée.", "success")
            return redirect(url_for("admin_sms"))

        if action in ("send_now", "schedule"):
            zone_id = (request.form.get("zone_id") or "").strip()
            polling_center = (request.form.get("polling_center") or "").strip()
            status_filter = (request.form.get("status_filter") or "").strip()
            only_missing_voter = bool(request.form.get("only_missing_voter") == "on")
            message = (request.form.get("message") or "").strip()
            scheduled_at = (request.form.get("scheduled_at") or "").strip()

            if not message:
                flash("Message requis.", "warning")
                return redirect(url_for("admin_sms"))

            if action == "send_now":
                # immediate campaign
                camps = _get_sms_campaigns()
                camp = {
                    "id": str(uuid.uuid4()),
                    "created_at": _now_iso(),
                    "created_by": u["id"],
                    "zone_id": zone_id,
                    "polling_center": polling_center,
                    "status_filter": status_filter,
                    "only_missing_voter": only_missing_voter,
                    "message": message,
                    "scheduled_at": _now_iso(),
                    "status": "SCHEDULED",
                    "sent_count": 0,
                    "total_count": 0,
                }
                camps.append(camp)
                _save_sms_campaigns(camps)
                _audit("sms.schedule", u["id"], "sms", camp["id"], {"now": True})
                flash("Campagne créée. Elle va être envoyée (par lots).", "success")
                _process_due_campaigns(u["id"])
                return redirect(url_for("admin_sms"))

            # schedule
            try:
                _ = _dt_from_iso(scheduled_at)
            except Exception:
                flash("Date/heure programmée invalide (format ISO). Exemple: 2028-04-01T18:00:00+00:00", "warning")
                return redirect(url_for("admin_sms"))

            camps = _get_sms_campaigns()
            camp = {
                "id": str(uuid.uuid4()),
                "created_at": _now_iso(),
                "created_by": u["id"],
                "zone_id": zone_id,
                "polling_center": polling_center,
                "status_filter": status_filter,
                "only_missing_voter": only_missing_voter,
                "message": message,
                "scheduled_at": scheduled_at,
                "status": "SCHEDULED",
                "sent_count": 0,
                "total_count": 0,
            }
            camps.append(camp)
            _save_sms_campaigns(camps)
            _audit("sms.schedule", u["id"], "sms", camp["id"], {"now": False})
            flash("Campagne programmée.", "success")
            return redirect(url_for("admin_sms"))

        if action == "run_due":
            _process_due_campaigns(u["id"])
            flash("Traitement des campagnes en attente terminé (ou limité par sécurité).", "success")
            return redirect(url_for("admin_sms"))

    camps = _get_sms_campaigns()
    camps_sorted = sorted(camps, key=lambda c: c.get("created_at") or "", reverse=True)

    return render_template(
        "admin/sms.html",
        cfg=cfg,
        zones=zones,
        centers=centers,
        camps=camps_sorted[:50],
        statuses=[STATUS_PENDING, STATUS_VERIFIED, STATUS_APPROVED, STATUS_REJECTED, STATUS_NEEDS_CORRECTION],
    )


# ----------------------------
# Payroll admin
# ----------------------------

@app.route("/admin/payroll", methods=["GET"])
@role_required("admin")
def admin_payroll():
    users = _get_users()
    agents = [u for u in users if u.get("role") == "agent" and u.get("is_active", True)]
    agents = sorted(agents, key=lambda x: x.get("full_name") or "")

    # Search by payment number
    payment_number = (request.args.get("payment_number") or "").strip()
    found = None
    if payment_number:
        items = _get_payroll()
        for it in items:
            if (it.get("payment_number") or "").strip().upper() == payment_number.strip().upper() or (it.get("id") or "") == payment_number:
                found = it
                break

    return render_template("admin/payroll_search.html", agents=agents, found=found, find_user=_find_user)


@app.route("/admin/payroll/user/<user_id>", methods=["GET", "POST"])
@role_required("admin")
def admin_payroll_user(user_id: str):
    u = current_user()
    target = _find_user(user_id)
    if not target or target.get("role") != "agent":
        abort(404)

    regs = _get_regs()
    payroll_items = _get_payroll()

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "").strip()

        if action == "generate":
            start_iso = (request.form.get("period_start") or "").strip()
            end_iso = (request.form.get("period_end") or "").strip()
            rec = _find_payslip(user_id, start_iso, end_iso, payroll_items)
            if rec and rec.get("is_locked"):
                flash("Cette période est verrouillée (fiche déjà générée).", "warning")
                return redirect(url_for("admin_payroll_user", user_id=user_id))

            periods = _periods_for_user(user_id, regs)
            p = next((x for x in periods if x["start_iso"] == start_iso and x["end_iso"] == end_iso), None)
            if not p:
                flash("Période invalide.", "danger")
                return redirect(url_for("admin_payroll_user", user_id=user_id))

            count = _count_regs_in_period(user_id, regs, p["start"], p["end"])
            approved_count = _count_approved_regs_in_period(user_id, regs, p["start"], p["end"])
            rate = int(_pay_rate_cfa())
            base_amount = int(count) * rate
            fixed_bonus = int(_pay_fixed_bonus_cfa()) if int(approved_count) >= 50 else 0
            gross = int(base_amount + fixed_bonus)
            advance = _sum_advances(user_id, payroll_items, start_iso, end_iso)
            balance = max(0, gross - advance)

            if rec:
                # update only if not locked
                rec["count"] = count
                rec["rate"] = rate
                rec["base_amount"] = base_amount
                rec["fixed_bonus_amount"] = fixed_bonus
                rec["gross_amount"] = gross
                rec["advance_amount"] = advance
                rec["balance_amount"] = balance
                rec["amount"] = balance
                rec["generated_at"] = _now_iso()
                rec["status"] = "GENERATED"
                rec["is_locked"] = True
                rec["locked_at"] = _now_iso()
                _audit("payroll.regenerate", u["id"], "payslip", rec["id"], {"period": [start_iso, end_iso]})
                flash("Fiche mise à jour et verrouillée.", "success")
            else:
                pay_id = str(uuid.uuid4())
                rec = {
                    "id": pay_id,
                    "type": "PAYSLIP",
                    "payment_number": _next_payment_number(payroll_items),
                    "user_id": user_id,
                    "period_start": start_iso,
                    "period_end": end_iso,
                    "count": count,
                    "rate": rate,
                    "base_amount": base_amount,
                    "fixed_bonus_amount": fixed_bonus,
                    "gross_amount": gross,
                    "advance_amount": advance,
                    "balance_amount": balance,
                    "amount": balance,
                    "generated_at": _now_iso(),
                    "generated_by": u["id"],
                    "status": "GENERATED",
                    "paid_at": "",
                    "paid_by": "",
                    "notes": "",
                    "is_locked": True,
                    "locked_at": _now_iso(),
                }
                payroll_items.append(rec)
                _audit("payroll.generate", u["id"], "payslip", pay_id, {"period": [start_iso, end_iso]})
                flash("Fiche générée et verrouillée.", "success")

            _save_payroll(payroll_items)
            return redirect(url_for("admin_payslip", pay_id=rec["id"]))

        if action == "generate_supplement":
            start_iso = (request.form.get("period_start") or "").strip()
            end_iso = (request.form.get("period_end") or "").strip()

            periods = _periods_for_user(user_id, regs)
            p = next((x for x in periods if x["start_iso"] == start_iso and x["end_iso"] == end_iso), None)
            if not p:
                flash("Période invalide.", "danger")
                return redirect(url_for("admin_payroll_user", user_id=user_id))

            total_count = _count_regs_in_period(user_id, regs, p["start"], p["end"])
            approved_total = _count_approved_regs_in_period(user_id, regs, p["start"], p["end"])
            rate = int(_pay_rate_cfa())
            base_total = int(total_count) * rate
            fixed_bonus_total = int(_pay_fixed_bonus_cfa()) if int(approved_total) >= 50 else 0
            gross_total = int(base_total + fixed_bonus_total)
            advance_total = _sum_advances(user_id, payroll_items, start_iso, end_iso)
            due_total = max(0, gross_total - advance_total)

            slips = _find_payslips(user_id, start_iso, end_iso, payroll_items)
            sum_balance = 0
            sum_count = 0
            for s in slips:
                try:
                    sum_balance += max(0, int(s.get("balance_amount", s.get("amount", 0)) or 0))
                except Exception:
                    pass
                try:
                    sum_count += max(0, int(s.get("count", 0) or 0))
                except Exception:
                    pass

            remaining_due = max(0, due_total - sum_balance)
            remaining_count = max(0, total_count - sum_count)

            if remaining_due <= 0:
                flash("Aucun complément à générer pour cette période.", "info")
                return redirect(url_for("admin_payroll_user", user_id=user_id))

            pay_id = str(uuid.uuid4())
            # Complément : peut servir à payer des dossiers ajoutés après une fiche,
            # ou à rattraper une prime fixe si elle a été activée après coup.
            supp_count = max(0, int(remaining_count))
            supp_base = int(supp_count) * int(rate)
            supp_bonus = max(0, int(remaining_due) - int(supp_base))
            supp_gross = int(supp_base + supp_bonus)

            rec = {
                "id": pay_id,
                "type": "PAYSLIP_SUPP",
                "payment_number": _next_payment_number(payroll_items),
                "user_id": user_id,
                "period_start": start_iso,
                "period_end": end_iso,
                "count": supp_count,
                "rate": int(rate),
                "base_amount": int(supp_base),
                "fixed_bonus_amount": int(supp_bonus),
                "gross_amount": int(supp_gross),
                "advance_amount": 0,
                "balance_amount": int(remaining_due),
                "amount": int(remaining_due),
                "generated_at": _now_iso(),
                "generated_by": u["id"],
                "status": "GENERATED",
                "paid_at": "",
                "paid_by": "",
                "notes": "Complément",
                "is_locked": True,
                "locked_at": _now_iso(),
            }
            payroll_items.append(rec)
            _save_payroll(payroll_items)
            _audit("payroll.generate_supplement", u["id"], "payslip", pay_id, {"period": [start_iso, end_iso]})
            flash("Complément généré et verrouillé.", "success")
            return redirect(url_for("admin_payslip", pay_id=rec["id"]))

        if action == "add_advance":
            start_iso = (request.form.get("period_start") or "").strip()
            end_iso = (request.form.get("period_end") or "").strip()
            amount_raw = (request.form.get("advance_amount") or "").strip()

            # The table displays inclusive end dates (end_exclusive - 1 day).
            # Many users will copy that visible date into the form.
            # Here we normalize to the internal end_exclusive value when possible.
            if start_iso and end_iso:
                try:
                    periods_all = _periods_for_user(user_id, regs)
                    p = next((x for x in periods_all if x.get("start_iso") == start_iso), None)
                    if p:
                        try:
                            inclusive = (date.fromisoformat(p["end_iso"]) - timedelta(days=1)).isoformat()
                        except Exception:
                            inclusive = ""
                        if inclusive and end_iso == inclusive:
                            end_iso = p["end_iso"]
                except Exception:
                    # keep as is
                    pass
            try:
                amt = int(amount_raw)
            except Exception:
                amt = 0
            if amt <= 0:
                flash("Montant d'avance invalide.", "warning")
                return redirect(url_for("admin_payroll_user", user_id=user_id))

            adv = {
                "id": str(uuid.uuid4()),
                "type": "ADVANCE",
                "payment_number": _next_payment_number(payroll_items),
                "user_id": user_id,
                "period_start": start_iso,
                "period_end": end_iso,
                "amount": int(amt),
                "created_at": _now_iso(),
                "created_by": u["id"],
                "status": "PAID",
                "paid_at": _now_iso(),
                "paid_by": u["id"],
                "notes": "Avance",
                "is_locked": True,
                "locked_at": _now_iso(),
            }
            payroll_items.append(adv)

            # If a payslip for this period already exists (even locked),
            # refresh its advance/balance amounts so advances are effectively deducted.
            ps = _find_payslip(user_id, start_iso, end_iso, payroll_items)
            if ps and (ps.get("status") or "").upper() != "PAID":
                try:
                    gross_amount = int(ps.get("gross_amount", 0) or 0)
                except Exception:
                    gross_amount = 0
                total_adv = _sum_advances(user_id, payroll_items, start_iso, end_iso)
                balance_amount = max(0, gross_amount - total_adv)
                ps["advance_amount"] = total_adv
                ps["balance_amount"] = balance_amount
                ps["amount"] = balance_amount
                ps["updated_at"] = _now_iso()

            _save_payroll(payroll_items)
            _audit("payroll.advance", u["id"], "advance", adv["id"], {"amount": amt, "period": [start_iso, end_iso]})
            flash("Avance enregistrée.", "success")
            return redirect(url_for("admin_payroll_user", user_id=user_id))

    # compute periods
    periods = _periods_for_user(user_id, regs)
    periods = periods[-24:]  # show last

    payroll_changed = False
    rows: List[Dict[str, Any]] = []
    for p in periods:
        start_iso, end_iso = p["start_iso"], p["end_iso"]
        count = _count_regs_in_period(user_id, regs, p["start"], p["end"])
        if count <= 0:
            continue
        approved_count = _count_approved_regs_in_period(user_id, regs, p["start"], p["end"])
        rate = int(_pay_rate_cfa())
        base_amount = int(count) * rate
        fixed_bonus = int(_pay_fixed_bonus_cfa()) if int(approved_count) >= 50 else 0
        gross = int(base_amount + fixed_bonus)
        advance = _sum_advances(user_id, payroll_items, start_iso, end_iso)
        balance = max(0, gross - advance)
        slips = _find_payslips(user_id, start_iso, end_iso, payroll_items)
        rec_primary = _find_payslip(user_id, start_iso, end_iso, payroll_items)
        rec_latest = slips[-1] if slips else None

        # Compute remaining due for this period (ex: new registrations after a payslip was paid)
        sum_balance = 0
        sum_count = 0
        paid_balance = 0
        paid_count = 0
        last_paid_at = ""
        for s in slips:
            try:
                bal = max(0, int(s.get("balance_amount", s.get("amount", 0)) or 0))
                sum_balance += bal
            except Exception:
                bal = 0
            try:
                cnt = max(0, int(s.get("count", 0) or 0))
                sum_count += cnt
            except Exception:
                cnt = 0

            if (s.get("status") or "").upper() == "PAID":
                paid_balance += bal
                paid_count += cnt
                pa = (s.get("paid_at") or "").strip()
                if pa and (not last_paid_at or pa > last_paid_at):
                    last_paid_at = pa

        remaining_due = max(0, balance - sum_balance)
        remaining_count = max(0, count - sum_count)
        due_now = max(0, balance - paid_balance)
        due_now_count = max(0, count - paid_count)

        if not slips:
            status = "NOT_GENERATED"
        elif any((s.get("status") or "").upper() != "PAID" for s in slips):
            status = "GENERATED"
        elif remaining_due > 0:
            status = "PARTIAL"
        else:
            status = "PAID"

        # Backward-compatible fix: older advances may have been saved with
        # inclusive period_end values, which previously prevented deductions.
        # Refresh existing payslips (not PAID) to reflect the correct advance/balance.
        if rec_primary and (rec_primary.get("status") or "").upper() != "PAID":
            try:
                locked_gross = int(rec_primary.get("gross_amount", gross) or 0)
            except Exception:
                locked_gross = gross
            total_adv = _sum_advances(user_id, payroll_items, start_iso, end_iso)
            new_balance = max(0, locked_gross - total_adv)
            if int(rec_primary.get("advance_amount", 0) or 0) != int(total_adv) or int(rec_primary.get("balance_amount", 0) or 0) != int(new_balance):
                rec_primary["advance_amount"] = int(total_adv)
                rec_primary["balance_amount"] = int(new_balance)
                rec_primary["amount"] = int(new_balance)
                rec_primary["updated_at"] = _now_iso()
                payroll_changed = True

        # Prefer locked amounts for display when a payslip exists,
        # so the table matches the generated PDF.
        display_count = int(rec_primary.get("count", count) or count) if rec_primary else count
        try:
            display_gross = int(rec_primary.get("gross_amount", gross) or gross) if rec_primary else gross
        except Exception:
            display_gross = gross
        display_advance = int(rec_primary.get("advance_amount", advance) or advance) if rec_primary else advance
        display_balance = int(rec_primary.get("balance_amount", balance) or balance) if rec_primary else balance

        rows.append({
            "start_iso": start_iso,
            "end_iso": end_iso,
            "label": _period_label(start_iso, end_iso),
            "count": display_count,
            "base_amount": int(rec_primary.get('base_amount', base_amount) or base_amount) if rec_primary else int(base_amount),
            "fixed_bonus": int(rec_primary.get('fixed_bonus_amount', fixed_bonus) or fixed_bonus) if rec_primary else int(fixed_bonus),
            "gross": display_gross,
            "advance": display_advance,
            "balance": display_balance,
            "status": status,
            "payslip": rec_latest,
            "remainder_due": int(remaining_due),
            "remainder_count": int(remaining_count),
            "paid_amount": int(paid_balance),
            "paid_count": int(paid_count),
            "due_now": int(due_now),
            "due_now_count": int(due_now_count),
            "last_paid_at": last_paid_at,
        })

    if payroll_changed:
        _save_payroll(payroll_items)

    # show recent advances
    advances = [x for x in payroll_items if x.get("type") == "ADVANCE" and x.get("user_id") == user_id]
    advances = sorted(advances, key=lambda x: x.get("created_at") or "", reverse=True)[:30]

    tab = (request.args.get("tab") or "upcoming").strip().lower()
    if tab not in ("upcoming", "paid"):
        tab = "upcoming"

    # Upcoming rows are period-level (what remains to be paid).
    upcoming_rows = [r for r in rows if r.get("status") != "PAID"]

    # Paid rows must be payment-level (each payslip has its own paid_at).
    paid_rows: List[Dict[str, Any]] = []
    for s in payroll_items:
        if s.get("type") not in PAYSLIP_TYPES:
            continue
        if s.get("user_id") != user_id:
            continue
        if (s.get("status") or "").upper() != "PAID":
            continue
        paid_at = (s.get("paid_at") or "").strip()
        if not paid_at:
            continue

        try:
            amt = int(s.get("balance_amount", s.get("amount", 0)) or 0)
        except Exception:
            amt = 0
        try:
            cnt = int(s.get("count", 0) or 0)
        except Exception:
            cnt = 0

        paid_rows.append({
            "id": s.get("id"),
            "label": f"{_period_label(s.get('period_start',''), s.get('period_end',''))} ({s.get('payment_number')})",
            "count": cnt,
            "amount": amt,
            "paid_at": paid_at,
        })

    paid_rows = sorted(paid_rows, key=lambda x: x.get("paid_at") or "", reverse=True)

    paid_total = 0
    for r in paid_rows:
        try:
            paid_total += int(r.get("amount", 0) or 0)
        except Exception:
            pass

    upcoming_total = 0
    for r in upcoming_rows:
        try:
            upcoming_total += int(r.get("due_now", r.get("balance", 0)) or 0)
        except Exception:
            pass

    return render_template(
        "admin/payroll_user.html",
        target=target,
        zone_name=_zone_name(target.get("zone_id")),
        tab=tab,
        paid_rows=paid_rows,
        upcoming_rows=upcoming_rows,
        paid_total=paid_total,
        upcoming_total=upcoming_total,
        rows=rows,
        advances=advances,
    )


@app.route("/admin/payroll/export.csv")
@role_required("admin")
def admin_payroll_export_csv():
    items = _get_payroll()
    # export payslips only
    rows = [x for x in items if x.get("type") in PAYSLIP_TYPES]
    rows = sorted(rows, key=lambda x: x.get("generated_at") or "", reverse=True)

    import csv

    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["payment_number", "user", "period_start", "period_end", "count", "rate", "base_amount", "fixed_bonus", "gross", "advance", "balance", "status", "paid_at"])
    for r in rows:
        user = _find_user(r.get("user_id"))
        w.writerow([
            r.get("payment_number"),
            (user.get("full_name") if user else r.get("user_id")),
            r.get("period_start"),
            r.get("period_end"),
            r.get("count"),
            r.get("rate"),
            r.get("base_amount"),
            r.get("fixed_bonus_amount"),
            r.get("gross_amount"),
            r.get("advance_amount"),
            r.get("balance_amount"),
            r.get("status"),
            r.get("paid_at"),
        ])

    data = buf.getvalue().encode("utf-8")
    return send_file(io.BytesIO(data), as_attachment=True, download_name="payroll_export.csv", mimetype="text/csv")


@app.route("/admin/payroll/payslip/<pay_id>", methods=["GET", "POST"])
@role_required("admin")
def admin_payslip(pay_id: str):
    payroll_items = _get_payroll()
    rec = next((x for x in payroll_items if x.get("id") == pay_id), None)
    if not rec:
        abort(404)

    target = _find_user(rec.get("user_id"))
    if not target:
        abort(404)

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)
        action = (request.form.get("action") or "").strip()
        if action == "mark_paid":
            rec["status"] = "PAID"
            rec["paid_at"] = _now_iso()
            rec["paid_by"] = current_user()["id"]
            rec["is_locked"] = True
            rec["locked_at"] = rec.get("locked_at") or _now_iso()
            _save_payroll(payroll_items)
            _audit("payroll.mark_paid", current_user()["id"], "payslip", pay_id, {})
            flash("Paiement marqué comme effectué.", "success")
        elif action == "mark_unpaid":
            # do not unlock period, but revert status
            rec["status"] = "GENERATED"
            rec["paid_at"] = ""
            rec["paid_by"] = ""
            _save_payroll(payroll_items)
            _audit("payroll.mark_unpaid", current_user()["id"], "payslip", pay_id, {})
            flash("Paiement remis en non-payé.", "warning")

        return redirect(url_for("admin_payslip", pay_id=pay_id))

    return render_template(
        "admin/payslip.html",
        target=target,
        zone_name=_zone_name(target.get("zone_id")),
        rec=rec,
        period_label=_period_label(rec.get("period_start", ""), rec.get("period_end", "")) if rec.get("type") in PAYSLIP_TYPES else "Avance",
        amount_fmt=_format_money_cfa(int(rec.get("amount", 0) or 0)),
        gross_fmt=_format_money_cfa(int(rec.get("gross_amount", rec.get("amount", 0)) or 0)),
        advance_fmt=_format_money_cfa(int(rec.get("advance_amount", 0) or 0)),
        balance_fmt=_format_money_cfa(int(rec.get("balance_amount", rec.get("amount", 0)) or 0)),
        base_fmt=_format_money_cfa(int(rec.get("base_amount", int(rec.get('count',0) or 0) * int(rec.get('rate', _pay_rate_cfa()) or _pay_rate_cfa())) or 0)),
        bonus_fmt=_format_money_cfa(int(rec.get("fixed_bonus_amount", 0) or 0)),
        rate=int(rec.get('rate', _pay_rate_cfa()) or _pay_rate_cfa()),
    )


@app.route("/admin/payroll/payslip/<pay_id>/pdf", methods=["GET"])
@role_required("admin")
def admin_payslip_pdf(pay_id: str):
    payroll_items = _get_payroll()
    rec = next((x for x in payroll_items if x.get("id") == pay_id), None)
    if not rec:
        abort(404)

    target = _find_user(rec.get("user_id"))
    if not target:
        abort(404)

    try:
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.units import mm
        from reportlab.lib import colors
        from reportlab.pdfgen import canvas
    except ModuleNotFoundError:
        flash("Le module 'reportlab' n'est pas installé dans ton environnement. Exécute: pip install -r requirements.txt", "danger")
        return redirect(url_for("admin_payslip", pay_id=pay_id))

    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=A4)
    w, h = A4

    accent = colors.HexColor("#f97316")
    dark = colors.HexColor("#111827")
    gray = colors.HexColor("#4b5563")

    left = 18 * mm
    right = w - 18 * mm
    top = h - 18 * mm

    c.setFillColor(accent)
    c.rect(0, h - 6, w, 6, stroke=0, fill=1)

    c.setFillColor(dark)
    c.setFont("Helvetica-Bold", 20)
    c.drawString(left, top + 2 * mm, "Recensement")
    c.setFont("Helvetica", 10)
    c.setFillColor(gray)
    c.drawString(left, top - 6 * mm, "support@recensement2028.local")
    c.drawString(left, top - 11 * mm, "+225 00 00 00 00 00")

    c.setFillColor(accent)
    c.setFont("Helvetica-Bold", 22)
    c.drawRightString(right, top + 2 * mm, "REÇU DE PAIEMENT")
    c.setFillColor(dark)
    c.setFont("Helvetica", 12)
    pay_no = rec.get("payment_number") or rec.get("id", "")
    c.drawRightString(right, top - 7 * mm, f"N°: {pay_no}")

    c.setFillColor(accent)
    c.rect(0, top - 18 * mm, w, 6, stroke=0, fill=1)

    y = top - 30 * mm
    c.setFillColor(dark)
    c.setFont("Helvetica-Bold", 12)
    c.drawString(left, y, "INFORMATIONS MARCHAND")
    c.drawRightString(right, y, "INFORMATIONS AGENT")

    c.setFont("Helvetica", 10)
    c.setFillColor(dark)

    y2 = y - 10 * mm
    c.drawString(left, y2, "Entreprise : Recensement Électoral 2028")
    c.drawString(left, y2 - 6 * mm, "Adresse : Bonoua")
    c.drawString(left, y2 - 12 * mm, "Téléphone : +225 00 00 00 00 00")

    c.drawRightString(right, y2, f"Nom : {target.get('full_name')}")
    c.drawRightString(right, y2 - 6 * mm, f"Zone : {_zone_name(target.get('zone_id'))}")

    if rec.get("type") in PAYSLIP_TYPES:
        c.drawRightString(right, y2 - 12 * mm, f"Période : {_period_label(rec.get('period_start',''), rec.get('period_end',''))}")

    c.setStrokeColor(colors.HexColor("#e5e7eb"))
    c.setLineWidth(1)
    c.line(left, y2 - 20 * mm, right, y2 - 20 * mm)

    y3 = y2 - 32 * mm
    c.setFont("Helvetica-Bold", 12)
    c.setFillColor(dark)
    c.drawString(left, y3, "DÉTAILS")

    c.setFont("Helvetica", 10)
    c.setFillColor(dark)

    count = int(rec.get("count", 0) or 0)
    rate = int(rec.get("rate", _pay_rate_cfa()) or _pay_rate_cfa())
    base_amount = int(rec.get("base_amount", count * rate) or 0)
    fixed_bonus = int(rec.get("fixed_bonus_amount", 0) or 0)
    gross = int(rec.get("gross_amount", base_amount + fixed_bonus) or 0)
    advance = int(rec.get("advance_amount", 0) or 0)
    balance = int(rec.get("balance_amount", rec.get("amount", 0)) or 0)

    lines = []
    if rec.get("type") in PAYSLIP_TYPES:
        lines.append(("Personnes recensées", str(count)))
        lines.append(("Tarif", f"{rate} F CFA"))
        lines.append(("Montant de base", _format_money_cfa(base_amount)))
        lines.append(("Prime fixe", _format_money_cfa(fixed_bonus)))
        lines.append(("Montant brut", _format_money_cfa(gross)))
        if advance:
            lines.append(("Avance(s)", f"- {_format_money_cfa(advance)}"))
        lines.append(("Net à payer", _format_money_cfa(balance)))
    else:
        lines.append(("Avance", _format_money_cfa(int(rec.get("amount", 0) or 0))))

    yy = y3 - 10 * mm
    for k, v in lines:
        c.setFont("Helvetica", 10)
        c.drawString(left, yy, k)
        c.setFont("Helvetica-Bold", 10)
        c.drawRightString(right, yy, v)
        yy -= 7 * mm

    c.setFillColor(accent)
    c.setFont("Helvetica-Bold", 16)
    c.drawRightString(right, yy - 6 * mm, f"TOTAL: {_format_money_cfa(int(rec.get('amount',0) or 0))}")

    c.setFillColor(gray)
    c.setFont("Helvetica", 9)
    c.drawString(left, 18 * mm, f"Généré le {_now_iso()[:19].replace('T',' ')}")

    c.showPage()
    c.save()

    buf.seek(0)
    filename = f"recu_{_safe_filename(pay_no)}.pdf"
    return send_file(buf, as_attachment=True, download_name=filename, mimetype="application/pdf")


# ----------------------------
# Supervisor routes
# ----------------------------

@app.route("/supervisor")
@role_required("supervisor")
def supervisor_dashboard():
    u = current_user()
    if not u.get("zone_id"):
        flash("Ton compte n'a pas de zone assignée. Demande à l'admin.", "danger")
        return redirect(url_for("index"))

    regs = _get_regs()
    in_zone = [r for r in regs if r.get("zone_id") == u.get("zone_id")]

    pending = [r for r in in_zone if r.get("status") == STATUS_PENDING]
    needs = [r for r in in_zone if r.get("status") == STATUS_NEEDS_CORRECTION]
    verified = [r for r in in_zone if r.get("status") == STATUS_VERIFIED]
    approved = [r for r in in_zone if r.get("status") == STATUS_APPROVED]
    rejected = [r for r in in_zone if r.get("status") == STATUS_REJECTED]

    counts = {
        "pending": len(pending),
        "needs": len(needs),
        "verified": len(verified),
        "approved": len(approved),
        "rejected": len(rejected),
        "total": len(in_zone),
    }

    pending_sorted = sorted(pending, key=lambda r: r.get("created_at") or "", reverse=True)[:200]
    needs_sorted = sorted(needs, key=lambda r: r.get("updated_at") or r.get("created_at") or "", reverse=True)[:200]
    verified_sorted = sorted(verified, key=lambda r: r.get("verified_at") or r.get("updated_at") or r.get("created_at") or "", reverse=True)[:200]
    approved_sorted = sorted(approved, key=lambda r: r.get("approved_at") or r.get("admin_approved_at") or r.get("updated_at") or r.get("created_at") or "", reverse=True)[:200]
    rejected_sorted = sorted(rejected, key=lambda r: r.get("rejected_at") or r.get("admin_rejected_at") or r.get("updated_at") or r.get("created_at") or "", reverse=True)[:200]
    return render_template(
        "supervisor/dashboard.html",
        counts=counts,
        pending=pending_sorted,
        needs=needs_sorted,
        verified=verified_sorted,
        approved=approved_sorted,
        rejected=rejected_sorted,
        zone_name=_zone_name(u.get("zone_id")),
        find_user=_find_user,
        format_date=_format_date,
    )


@app.route("/supervisor/registration/<reg_id>", methods=["GET", "POST"])
@role_required("supervisor")
def supervisor_review(reg_id: str):
    u = current_user()
    regs = _get_regs()
    reg = next((r for r in regs if r.get("id") == reg_id), None)
    if not reg:
        abort(404)

    if reg.get("zone_id") != u.get("zone_id"):
        abort(403)

    centers_map = _get_centers_map()
    # Pour la validation superviseur : afficher tous les centres de vote,
    # car un électeur peut voter dans un centre différent de sa zone de résidence.
    centers: List[Dict[str, Any]] = []
    for v in centers_map.values():
        if isinstance(v, list):
            centers.extend(v)
    # Tri par nom pour une liste plus lisible
    centers = sorted(centers, key=lambda c: (c.get("name") or c.get("centre_name") or "").strip())

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        # Si l'admin a déjà approuvé/rejeté/marqué payé, le superviseur ne peut plus modifier.
        if _admin_done(reg):
            flash("Dossier déjà traité par l’admin (approuvé/rejeté/payé) : modification superviseur interdite.", "warning")
            return redirect(url_for("supervisor_review", reg_id=reg_id))

        before = _deepcopy_json(reg)

        action = (request.form.get("action") or "").strip()
        voter_number = (request.form.get("voter_number") or "").strip()
        polling_center = (request.form.get("polling_center") or "").strip()
        polling_station = (request.form.get("polling_station") or "").strip()
        notes = (request.form.get("notes") or "").strip()
        correction_reason = (request.form.get("correction_reason") or "").strip()

        if action == "verify":
            if not (voter_number and polling_center and polling_station):
                flash("Pour valider : numéro d’électeur, centre et bureau sont requis.", "warning")
                return render_template(
                    "supervisor/review.html",
                    reg=reg,
                    creator=_find_user(reg.get("created_by")),
                    zone_name=_zone_name(reg.get("zone_id")),
                    format_date=_format_date,
                    centers=centers,
                )

            # Canonicalise le centre (évite les variations de casse/accents/espaces
            # qui cassent les stats et la carte).
            matched_center = _match_center_from_value(centers, polling_center)
            if not matched_center:
                flash("Centre de vote invalide : sélectionne un centre existant dans la liste.", "warning")
                return render_template(
                    "supervisor/review.html",
                    reg=reg,
                    creator=_find_user(reg.get("created_by")),
                    zone_name=_zone_name(reg.get("zone_id")),
                    format_date=_format_date,
                    centers=centers,
                )
            polling_center = matched_center.get("name") or polling_center
            polling_center_id = matched_center.get("id")

            # Détection de doublons (nom + prénoms + DOB + centre)
            dups = _find_duplicates(
                reg.get("nom") or "",
                reg.get("prenoms") or "",
                reg.get("dob") or "",
                polling_center,
                regs,
                zone_id=u.get("zone_id"),
                exclude_id=reg.get("id"),
                strict_center=True,
            )
            confirm_dup = (request.form.get("confirm_duplicate") or "").strip() == "yes"
            if dups and not confirm_dup:
                flash("Doublon probable détecté (même identité dans le même centre). Coche la confirmation si tu veux valider quand même.", "warning")
                return render_template(
                    "supervisor/review.html",
                    reg=reg,
                    creator=_find_user(reg.get("created_by")),
                    zone_name=_zone_name(reg.get("zone_id")),
                    format_date=_format_date,
                    centers=centers,
                    duplicates=dups,
                )

            reg["voter_number"] = voter_number
            reg["polling_center"] = polling_center
            reg["polling_center_id"] = polling_center_id
            reg["polling_station"] = polling_station
            reg["notes"] = notes

            # Horodatage unique pour tous les champs de validation
            now_iso = _now_iso()

            # Validation (superviseur)
            reg["verified_by"] = u["id"]
            reg["verified_at"] = now_iso
            reg["supervisor_status"] = STATUS_VERIFIED
            reg["supervisor_verified"] = True
            reg["supervisor_verified_by"] = u["id"]
            reg["supervisor_verified_at"] = now_iso

            # En mode double validation, le dossier DOIT passer par l'admin.
            # Force: any supervisor-verified dossier must pass through admin approvals
            double_approval = True
            reg["status"] = STATUS_VERIFIED
            reg["needs_admin_approval"] = True if double_approval else False
            if double_approval:
                _queue_for_admin(reg_id)

            # Compatibilité avec d'anciennes clés
            reg["need_admin_approval"] = reg["needs_admin_approval"]
            reg["awaiting_admin_approval"] = reg["needs_admin_approval"]
            reg["approval_stage"] = "PENDING_ADMIN" if reg["needs_admin_approval"] else ""

            # Réinitialise toujours les marqueurs admin tant que le dossier n'a pas été approuvé.
            reg["admin_approved"] = False
            reg["admin_approved_by"] = None
            reg["admin_approved_at"] = None

            # Score de fiabilité (mise à jour)
            sc, miss = _compute_reliability_score(reg)
            reg["reliability_score"] = sc
            reg["reliability_missing"] = miss

            _save_regs(regs)
            _audit_reg_change("reg.verify", u["id"], before, reg, {"status": reg.get("status")})
            flash("Enregistrement validé.", "success")
            return redirect(url_for("supervisor_dashboard"))

        if action == "reject":
            reg["status"] = STATUS_REJECTED
            _dequeue_for_admin(reg_id)
            reg["voter_number"] = ""
            reg["polling_center"] = ""
            reg["polling_center_id"] = ""
            reg["polling_station"] = ""
            reg["notes"] = notes
            reg["verified_by"] = u["id"]
            reg["verified_at"] = _now_iso()
            sc, miss = _compute_reliability_score(reg)
            reg["reliability_score"] = sc
            reg["reliability_missing"] = miss

            _save_regs(regs)
            _audit_reg_change("reg.reject", u["id"], before, reg, {"reason": notes})
            flash("Enregistrement rejeté.", "success")
            return redirect(url_for("supervisor_dashboard"))

        if action == "needs_correction":
            if not correction_reason:
                flash("Motif requis pour demander une correction.", "warning")
                return redirect(url_for("supervisor_review", reg_id=reg_id))
            reg["status"] = STATUS_NEEDS_CORRECTION
            _dequeue_for_admin(reg_id)
            reg["correction_reason"] = correction_reason
            reg["qc_notes"] = notes
            reg["verified_by"] = u["id"]
            reg["verified_at"] = _now_iso()
            sc, miss = _compute_reliability_score(reg)
            reg["reliability_score"] = sc
            reg["reliability_missing"] = miss

            _save_regs(regs)
            _audit_reg_change("reg.needs_correction", u["id"], before, reg, {"reason": correction_reason})
            flash("Correction demandée à l’agent.", "success")
            return redirect(url_for("supervisor_dashboard"))

        if action == "back_to_pending":
            reg["status"] = STATUS_PENDING
            reg["verified_by"] = ""
            reg["verified_at"] = ""
            reg["supervisor_verified"] = False
            reg["supervisor_verified_by"] = ""
            reg["supervisor_verified_at"] = ""
            reg["supervisor_status"] = ""
            reg["needs_admin_approval"] = False
            reg["need_admin_approval"] = False
            reg["awaiting_admin_approval"] = False
            reg["approval_stage"] = ""
            reg["admin_approved"] = False
            reg["admin_approved_by"] = None
            reg["admin_approved_at"] = None
            reg["approved_by"] = ""
            reg["approved_at"] = ""
            reg["voter_number"] = ""
            reg["polling_center"] = ""
            reg["polling_center_id"] = ""
            reg["polling_station"] = ""
            reg["notes"] = notes
            reg["qc_notes"] = ""
            reg["correction_reason"] = ""
            sc, miss = _compute_reliability_score(reg)
            reg["reliability_score"] = sc
            reg["reliability_missing"] = miss

            _save_regs(regs)
            _audit_reg_change("reg.reset_pending", u["id"], before, reg, {})
            flash("Enregistrement remis en attente.", "success")
            return redirect(url_for("supervisor_dashboard"))

    return render_template(
        "supervisor/review.html",
        reg=reg,
        creator=_find_user(reg.get("created_by")),
        zone_name=_zone_name(reg.get("zone_id")),
        format_date=_format_date,
        centers=centers,
    )

@app.route("/supervisor/registration/<reg_id>/history")
@role_required("supervisor")
def supervisor_registration_history(reg_id: str):
    u = current_user()
    regs = _get_regs()
    reg = next((r for r in regs if str(r.get("id")) == str(reg_id)), None)
    if not reg or str(reg.get("zone_id") or "") != str(u.get("zone_id") or ""):
        abort(404)

    logs = _get_audit()
    hist = [e for e in logs if (e.get("target_type") == "registration" and str(e.get("target_id")) == str(reg_id))]
    hist = _inject_admin_decision_events(reg, hist)
    hist = sorted(hist, key=lambda e: e.get("at") or "", reverse=True)

    for e in hist:
        e["_actor"] = _find_user(e.get("actor_id")) or {"full_name": e.get("actor_id") or "?"}

    # centers list for navigation context if needed
    zone_regs = [r for r in regs if str(r.get("zone_id") or "") == str(u.get("zone_id") or "")]
    centers = sorted({(r.get("polling_center") or "").strip() for r in zone_regs if (r.get("polling_center") or "").strip()})

    return render_template(
        "supervisor/registration_history.html",
        reg=reg,
        history=hist,
        zone_name=_zone_name,
        format_date=_format_date,
        centers=centers,
    )



# Supervisor SMS for zone
@app.route("/supervisor/sms", methods=["GET", "POST"])
@role_required("supervisor")
def supervisor_sms():
    u = current_user()
    _process_due_campaigns(u["id"])  # scheduled for this user too

    regs = _get_regs()
    zone_id = u.get("zone_id")
    in_zone = [r for r in regs if r.get("zone_id") == zone_id]
    centers = sorted({(r.get("polling_center") or "").strip() for r in in_zone if (r.get("polling_center") or "").strip()})

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "").strip()
        if action in ("send_now", "schedule"):
            polling_center = (request.form.get("polling_center") or "").strip()
            status_filter = (request.form.get("status_filter") or "").strip()
            only_missing_voter = bool(request.form.get("only_missing_voter") == "on")
            message = (request.form.get("message") or "").strip()
            scheduled_at = (request.form.get("scheduled_at") or "").strip()

            if not message:
                flash("Message requis.", "warning")
                return redirect(url_for("supervisor_sms"))

            camps = _get_sms_campaigns()
            camp = {
                "id": str(uuid.uuid4()),
                "created_at": _now_iso(),
                "created_by": u["id"],
                "zone_id": zone_id,
                "polling_center": polling_center,
                "status_filter": status_filter,
                "only_missing_voter": only_missing_voter,
                "message": message,
                "scheduled_at": _now_iso() if action == "send_now" else scheduled_at,
                "status": "SCHEDULED",
                "sent_count": 0,
                "total_count": 0,
            }
            if action == "schedule":
                try:
                    _ = _dt_from_iso(scheduled_at)
                except Exception:
                    flash("Date/heure programmée invalide (format ISO).", "warning")
                    return redirect(url_for("supervisor_sms"))

            camps.append(camp)
            _save_sms_campaigns(camps)
            _audit("sms.schedule", u["id"], "sms", camp["id"], {"role": "supervisor"})
            flash("Campagne créée.", "success")
            _process_due_campaigns(u["id"])
            return redirect(url_for("supervisor_sms"))

        if action == "run_due":
            _process_due_campaigns(u["id"])
            flash("Traitement terminé (ou limité par sécurité).", "success")
            return redirect(url_for("supervisor_sms"))

    camps = _get_sms_campaigns()
    camps_zone = [c for c in camps if (c.get("zone_id") or "") == zone_id]
    camps_zone = sorted(camps_zone, key=lambda c: c.get("created_at") or "", reverse=True)[:50]

    return render_template(
        "supervisor/sms.html",
        centers=centers,
        camps=camps_zone,
        statuses=[STATUS_PENDING, STATUS_VERIFIED, STATUS_APPROVED, STATUS_REJECTED, STATUS_NEEDS_CORRECTION],
    )


# ----------------------------
# Agent routes
# ----------------------------



@app.route("/agent/registration/<reg_id>/history")
@role_required("agent")
def agent_registration_history(reg_id: str):
    u = current_user()
    regs = _get_regs()
    reg = next((r for r in regs if str(r.get("id")) == str(reg_id)), None)
    if not reg or str(reg.get("created_by") or "") != str(u.get("id") or ""):
        abort(404)

    logs = _get_audit()
    hist = [e for e in logs if (e.get("target_type") == "registration" and str(e.get("target_id")) == str(reg_id))]
    hist = sorted(hist, key=lambda e: e.get("at") or "", reverse=True)

    for e in hist:
        e["_actor"] = _find_user(e.get("actor_id")) or {"full_name": e.get("actor_id") or "?"}

    return render_template(
        "agent/registration_history.html",
        reg=reg,
        history=hist,
        zone_name=_zone_name,
        format_date=_format_date,
    )
@app.route("/agent")
@role_required("agent")
def agent_dashboard():
    u = current_user()
    regs = _get_regs()
    mine = [r for r in regs if r.get("created_by") == u.get("id")]

    # counts
    counts = {
        "total": len(mine),
        "draft": sum(1 for r in mine if r.get("status") == STATUS_DRAFT),
        "pending": sum(1 for r in mine if r.get("status") == STATUS_PENDING),
        "needs": sum(1 for r in mine if r.get("status") == STATUS_NEEDS_CORRECTION),
        "verified": sum(1 for r in mine if r.get("status") == STATUS_VERIFIED),
        "approved": sum(1 for r in mine if r.get("status") == STATUS_APPROVED),
        "rejected": sum(1 for r in mine if r.get("status") == STATUS_REJECTED),
    }

    mine_sorted = sorted(mine, key=lambda r: r.get("created_at", ""), reverse=True)
    page = request.args.get("page", "1")
    pag = _paginate(mine_sorted, int(page) if str(page).isdigit() else 1, 10)

    # payroll preview
    payroll_items = _get_payroll()
    periods = _periods_for_user(u["id"], regs)

    # IMPORTANT: a payslip (or a supplement) is *locked* at generation time.
    # We therefore never recompute "paid" amounts from live registrations.
    # If new registrations arrive after a period has been generated/paid, they
    # are shown as a remaining amount to generate (and pay) later.
    pay_rows: List[Dict[str, Any]] = []
    for p in periods[-12:]:
        start_iso = p["start_iso"]
        end_iso = p["end_iso"]

        total_count = _count_regs_in_period(u["id"], regs, p["start"], p["end"])
        if total_count <= 0:
            continue

        gross_total = _calc_amount(total_count)
        advance_total = _sum_advances(u["id"], payroll_items, start_iso, end_iso)
        due_total = max(0, gross_total - advance_total)

        slips = _find_payslips(u["id"], start_iso, end_iso, payroll_items)
        sum_slip_balance = 0
        sum_slip_count = 0

        # Add explicit rows for each generated/paid payslip (primary + supplements)
        for rec in slips:
            st = (rec.get("status") or "GENERATED").strip() or "GENERATED"
            try:
                rec_count = int(rec.get("count", 0) or 0)
            except Exception:
                rec_count = 0
            try:
                rec_balance = int(rec.get("balance_amount", rec.get("amount", 0)) or 0)
            except Exception:
                rec_balance = int(rec.get("amount", 0) or 0)

            sum_slip_balance += max(0, rec_balance)
            sum_slip_count += max(0, rec_count)

            pay_no = (rec.get("payment_number") or "").strip()
            label = _period_label(start_iso, end_iso)
            # If there are multiple payslips for the same period, display the payment no.
            if pay_no and (len(slips) > 1 or rec.get("type") == "PAYSLIP_SUPP"):
                label = f"{label} ({pay_no})"

            pay_rows.append(
                {
                    "label": label,
                    "count": rec_count,
                    "gross": int(rec.get("gross_amount", 0) or 0),
                    "advance": int(rec.get("advance_amount", 0) or 0),
                    "amount": max(0, rec_balance),
                    "amount_fmt": _format_money_cfa(max(0, rec_balance)),
                    "status": st,
                    "paid_at": (rec.get("paid_at") if st == "PAID" else ""),
                }
            )

        # Remaining amount not yet generated (ex: new registrations after a period was paid)
        remaining_due = max(0, due_total - sum_slip_balance)
        remaining_count = max(0, total_count - sum_slip_count)
        if remaining_due > 0:
            pay_rows.append(
                {
                    "label": _period_label(start_iso, end_iso) + " (reste à payer)",
                    "count": remaining_count,
                    "gross": 0,
                    "advance": 0,
                    "amount": remaining_due,
                    "amount_fmt": _format_money_cfa(remaining_due),
                    "status": "NOT_GENERATED",
                    "paid_at": "",
                }
            )

    upcoming = [r for r in pay_rows if r["status"] != "PAID"]
    paid = [r for r in pay_rows if r["status"] == "PAID"]
    upcoming_total = sum(r["amount"] for r in upcoming)
    paid_total = sum(r["amount"] for r in paid)

    pay_tab = (request.args.get("pay_tab") or "upcoming").strip()
    if pay_tab not in ("upcoming", "paid"):
        pay_tab = "upcoming"

    return render_template(
        "agent/dashboard.html",
        regs=pag["items"],
        pagination=pag,
        counts=counts,
        zone_name=_zone_name(u.get("zone_id")),
        upcoming=upcoming,
        upcoming_total_fmt=_format_money_cfa(upcoming_total),
        paid=paid,
        paid_total_fmt=_format_money_cfa(paid_total),
        pay_tab=pay_tab,
    )


@app.route("/agent/duplicates/check", methods=["GET", "POST"])
@role_required("agent")
def agent_check_duplicates():
    u = current_user()

    # GET: utilisé par le JS (pré-alerte), pas de CSRF requis car lecture seule
    if request.method == "POST":
        if not _csrf_validate():
            abort(400)
        src = request.form
    else:
        src = request.args

    nom = (src.get("nom") or "").strip()
    prenoms = (src.get("prenoms") or "").strip()
    dob = (src.get("dob") or "").strip()
    polling_center = (src.get("polling_center") or "").strip()
    exclude_id = (src.get("exclude_id") or "").strip() or None

    regs = _get_regs()
    matches = _find_duplicates(
        nom,
        prenoms,
        dob,
        polling_center,
        regs,
        zone_id=u.get("zone_id"),
        exclude_id=exclude_id,
        strict_center=False,
    )

    # Reduce payload
    out = []
    for r in matches:
        out.append({
            "id": r.get("id"),
            "nom": r.get("nom"),
            "prenoms": r.get("prenoms"),
            "dob": r.get("dob"),
            "telephone": r.get("telephone"),
            "quartier": r.get("quartier"),
            "zone": _zone_name(r.get("zone_id")),
            "center": r.get("polling_center") or "",
            "status": r.get("status"),
        })

    return jsonify({"count": len(out), "matches": out})


@app.route("/agent/registration/new", methods=["GET", "POST"])
@role_required("agent")
def agent_new_registration():
    u = current_user()
    if not u.get("zone_id"):
        flash("Ton compte n'a pas de zone assignée. Demande à l'admin.", "danger")
        return redirect(url_for("agent_dashboard"))

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        action = (request.form.get("action") or "save").strip()  # save or draft

        nom = (request.form.get("nom") or "").strip()
        prenoms = (request.form.get("prenoms") or "").strip()
        dob = (request.form.get("dob") or "").strip()
        quartier = (request.form.get("quartier") or "").strip()
        telephone = (request.form.get("telephone") or "").strip()

        if not (nom and prenoms and dob and quartier and telephone):
            flash("Tous les champs sont obligatoires.", "warning")
            return render_template("agent/registration_new.html")

        regs = _get_regs()
        dups = _find_duplicates(
            nom,
            prenoms,
            dob,
            "",  # centre inconnu côté agent
            regs,
            zone_id=u.get("zone_id"),
            strict_center=False,
        )
        confirm_dup = (request.form.get("confirm_duplicate") or "").strip() == "yes"
        if dups and not confirm_dup:
            flash("Doublon probable détecté. Coche la confirmation si tu veux enregistrer quand même.", "warning")
            return render_template("agent/registration_new.html", form=request.form, duplicates=dups, format_date=_format_date)

        photos = []
        if request.files.get("photo") and request.files["photo"].filename:
            try:
                stored = _save_upload(request.files["photo"])
                photos.append(stored)
            except Exception as e:
                flash(str(e), "danger")
                return render_template("agent/registration_new.html", form=request.form, duplicates=dups, format_date=_format_date)

        status = STATUS_DRAFT if action == "draft" else STATUS_PENDING

        reg = {
            "id": str(uuid.uuid4()),
            "nom": nom,
            "prenoms": prenoms,
            "dob": dob,
            "quartier": quartier,
            "telephone": telephone,
            "zone_id": u["zone_id"],
            "created_by": u["id"],
            "created_at": _now_iso(),
            "updated_by": u["id"],
            "updated_at": _now_iso(),
            "voter_number": "",
            "polling_center": "",
            "polling_station": "",
            "status": status,
            "verified_by": "",
            "verified_at": "",
            "approved_by": "",
            "approved_at": "",
            "notes": "",
            "qc_notes": "",
            "correction_reason": "",
            "photos": photos,
            "sms_last_at": "",
        }
        # Score de fiabilité (mise à jour immédiate)
        sc, miss = _compute_reliability_score(reg)
        reg["reliability_score"] = sc
        reg["reliability_missing"] = miss

        regs.append(reg)
        _save_regs(regs)
        _audit_reg_change("reg.create", u["id"], None, reg, {"status": status})

        if status == STATUS_DRAFT:
            flash("Brouillon enregistré. Tu peux le compléter puis l'envoyer.", "success")
        else:
            flash("Enregistrement ajouté. Il sera vérifié par ton superviseur.", "success")

        return redirect(url_for("agent_dashboard"))

    return render_template("agent/registration_new.html", form=None, duplicates=None, format_date=_format_date)


@app.route("/agent/registration/<reg_id>/edit", methods=["GET", "POST"])
@role_required("agent")
def agent_edit_registration(reg_id: str):
    u = current_user()
    regs = _get_regs()
    reg = next((r for r in regs if r.get("id") == reg_id), None)
    if not reg:
        abort(404)
    if reg.get("created_by") != u.get("id"):
        abort(403)

    if reg.get("status") not in (STATUS_DRAFT, STATUS_NEEDS_CORRECTION):
        flash("Ce dossier n'est pas modifiable (déjà en traitement).", "warning")
        return redirect(url_for("agent_dashboard"))

    if request.method == "POST":
        if not _csrf_validate():
            abort(400)

        before = _deepcopy_json(reg)
        action = (request.form.get("action") or "save").strip()  # save_draft or submit

        reg["nom"] = (request.form.get("nom") or "").strip()
        reg["prenoms"] = (request.form.get("prenoms") or "").strip()
        reg["dob"] = (request.form.get("dob") or "").strip()
        reg["quartier"] = (request.form.get("quartier") or "").strip()
        reg["telephone"] = (request.form.get("telephone") or "").strip()

        if not (reg["nom"] and reg["prenoms"] and reg["dob"] and reg["quartier"] and reg["telephone"]):
            flash("Tous les champs sont obligatoires.", "warning")
            return render_template("agent/registration_edit.html", reg=reg, format_date=_format_date, duplicates=None)

        # Détection de doublons (avant enregistrement)
        dups = _find_duplicates(
            reg["nom"],
            reg["prenoms"],
            reg["dob"],
            "",  # centre inconnu côté agent
            regs,
            zone_id=u.get("zone_id"),
            exclude_id=reg.get("id"),
            strict_center=False,
        )
        confirm_dup = (request.form.get("confirm_duplicate") or "").strip() == "yes"
        if dups and not confirm_dup:
            flash("Doublon probable détecté. Coche la confirmation si tu veux enregistrer quand même.", "warning")
            return render_template("agent/registration_edit.html", reg=reg, format_date=_format_date, duplicates=dups)

        if request.files.get("photo") and request.files["photo"].filename:
            try:
                stored = _save_upload(request.files["photo"])
                reg.setdefault("photos", []).append(stored)
            except Exception as e:
                flash(str(e), "danger")
                return render_template("agent/registration_edit.html", reg=reg, format_date=_format_date, duplicates=dups)

        reg["updated_by"] = u["id"]
        reg["updated_at"] = _now_iso()

        if action == "submit":
            reg["status"] = STATUS_PENDING
            reg["qc_notes"] = ""
            reg["correction_reason"] = ""
            flash("Dossier envoyé au superviseur.", "success")
            act = "reg.submit"
        else:
            reg["status"] = STATUS_DRAFT
            flash("Brouillon mis à jour.", "success")
            act = "reg.update_draft"

        # Score de fiabilité (mise à jour)
        sc, miss = _compute_reliability_score(reg)
        reg["reliability_score"] = sc
        reg["reliability_missing"] = miss

        _audit_reg_change(act, u["id"], before, reg, {})
        _save_regs(regs)
        return redirect(url_for("agent_dashboard"))

    return render_template("agent/registration_edit.html", reg=reg, format_date=_format_date)


@app.route("/uploads/<filename>")
@login_required
def view_upload(filename: str):
    u = current_user()
    safe = secure_filename(filename)
    path = os.path.join(UPLOADS_DIR, safe)
    if not os.path.exists(path):
        abort(404)

    # Find any reg that references this file, and check permission
    regs = _get_regs()
    reg = next((r for r in regs if safe in (r.get("photos") or [])), None)
    if not reg:
        # Admin can still view
        if u.get("role") != "admin":
            abort(403)
    else:
        if not _can_view_reg(u, reg):
            abort(403)

    return send_file(path, as_attachment=False)


# ----------------------------
@app.route("/admin/backup/download/<name>")
@role_required("admin")
def admin_backup_download(name: str):
    safe = os.path.basename(name)
    path = os.path.join(BACKUPS_DIR, safe)
    if not os.path.isfile(path):
        abort(404)
    _audit("backup.download", current_user()["id"], "backup", safe, {})
    return send_file(path, as_attachment=True, download_name=safe)


# Errors
# ----------------------------

@app.errorhandler(403)
def forbidden(_):
    return render_template("errors/403.html"), 403


@app.errorhandler(404)
def not_found(_):
    return render_template("errors/404.html"), 404


@app.errorhandler(400)
def bad_request(_):
    return render_template("errors/400.html"), 400


# ----------------------------
# Main
# ----------------------------

if __name__ == "__main__":
    _ensure_data_files()
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "5000")), debug=True)
