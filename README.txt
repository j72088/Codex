Relentless Execution v7.9.5 - WIN BUILDER (Qt UI)

Quick start (what to click)
1) Unzip this folder anywhere
2) Double-click RUN_APP.bat

If you built the EXE and it closes instantly
- Double-click DEBUG_EXE.bat

Build the EXE
- Double-click BUILD_EXE.bat
  - If it fails, it will open build_exe.log automatically.
  - Do NOT open any PowerShell scripts manually.

Locked behavior reminders
- Supports Stocks + Crypto
- Crypto is LONG-only
- LIVE trading requires a typed confirmation inside the app
- Auto-connect happens on launch when keys exist
- PANIC: Flatten All cancels orders + closes positions (should not crash)

Where files are saved (persistence)
%APPDATA%\RelentlessExecution\
- keys, logs, settings, equity history, trade_events.csv, diagnostics, receipts, etc.

Optional helpers
- RELAX_FOR_TESTING.bat : enables relaxed PAPER gates (helps force lifecycle tests)
- RESTORE_SAFETY_DEFAULTS.bat : restores safer defaults
- SELF_TEST.bat : runs a non-destructive self-test
- EXPORT_DIAGNOSTICS.bat : creates a diagnostics zip under %APPDATA%\RelentlessExecution\diagnostics

Click rule (always)
- RUN_APP.bat to run
- BUILD_EXE.bat to build
- DEBUG_EXE.bat if the EXE closes


RUN_APP.bat now auto-installs Python dependencies into a local .venv on first run.
If it fails, open run_app.log in the project folder.


Update packaging
- After any code update, run `REZIP_PROJECT.bat` from the project folder to create a fresh downloadable zip archive with the current `.py/.bat/.txt` files and `requirements.txt`.
