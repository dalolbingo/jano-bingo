JANO BINGO — NEON POSTGRESQL MIGRATION BRANCH

Files:
- server.py: Python/FastAPI + Telegram bot backend
- index.html: Telegram Mini App frontend
- requirements.txt: pinned Python dependencies

Required Render environment variables:
- BOT_TOKEN: Telegram bot token (keep private)
- ADMIN_ID: numeric Telegram admin user ID
- APP_URL: public HTTPS URL of this deployment
- CORS_ORIGINS: comma-separated allowed origins; normally same as APP_URL
- DATABASE_URL: Neon PostgreSQL connection string (keep private)
- SUPPORT_USERNAME, TELEBIRR_NAME, TELEBIRR_PHONE: optional display settings
- MIN_PLAYERS: optional minimum players (default 2)

Do not set DB_PATH for this PostgreSQL build. The backend creates its tables and reference index in Neon at startup.

Run with exactly ONE worker/process because active game rooms remain in process memory:
  uvicorn server:app --host 0.0.0.0 --port 8000 --workers 1

Deploy server.py and index.html in the same working directory. Configure the Telegram bot Web App URL to APP_URL.

IMPORTANT LIMITATIONS BEFORE REAL-MONEY USE:
- This branch uses Neon PostgreSQL for persistent user accounts, balances, transactions, requests, and house statistics. Existing SQLite test data is not migrated; the Neon database starts fresh.
- Active game rooms, cards, called numbers, and live round state remain in process memory. A process restart or multiple server instances can interrupt a live round; deploy one process and do not restart during rounds. Persistent round recovery is not implemented.
- Money columns preserve the previous floating-point representation. A production money system should use integer minor units and an auditable ledger.
- Payment proof is reviewed manually by the admin; this app does not verify bank/TeleBirr transfers with a payment-provider API.
- The admin backup button now directs admins to Neon backup/restore tools; it does not send a local SQLite file.
- No independent penetration test, load test, or live payment test has been completed. Use test balances only until those are done and local legal requirements are confirmed.
