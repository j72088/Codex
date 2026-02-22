@echo off
setlocal

REM ==================================================
REM RELAX_FOR_TESTING.bat (PAPER ONLY)
REM
REM This enables a looser entry filter so you can generate
REM more PAPER trades for debugging / flow validation.
REM
REM What it does:
REM   - Enables RELAX signal (EMA tolerance + RSI thresholds)
REM   - Enables PAPER relax mode (lower min score, enables probe)
REM
REM To go back to strict behavior, just run RUN_APP.bat (no relax env vars).
REM ==================================================

set RELENTLESS_RELAX_SIGNAL=1
set RELENTLESS_PAPER_RELAX=1

echo [RELAX_FOR_TESTING] RELENTLESS_RELAX_SIGNAL=1
echo [RELAX_FOR_TESTING] RELENTLESS_PAPER_RELAX=1
echo.

call RUN_APP.bat

endlocal
