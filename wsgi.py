"""WSGI entrypoint for production servers (Gunicorn, uWSGI, etc.).

It ensures the JSON storage files exist before the app starts serving.
"""

from app import app, _ensure_data_files

_ensure_data_files()

application = app
