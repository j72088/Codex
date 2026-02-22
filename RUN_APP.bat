@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
setlocal EnableExtensions EnableDelayedExpansion
set WORKDIR=%~dp0
cd /d "%WORKDIR%"

set LOG=%WORKDIR%run_app.log
set SCRIPT=relentless_qt_gui_v8_11_2.py
set VENV_DIR=%USERPROFILE%\.relentless_venv

> "%LOG%" echo ==================================================
>>"%LOG%" echo RUN_APP started: %DATE% %TIME%
>>"%LOG%" echo Folder: %WORKDIR%
>>"%LOG%" echo Venv: %VENV_DIR%
>>"%LOG%" echo ==================================================
>>"%LOG%" echo Using script: %SCRIPT%
>>"%LOG%" echo.

rem ---- Find Python (prefer python, fallback to py -3) ----
set PY_CMD=python
where python >nul 2>nul
if errorlevel 1 (
  where py >nul 2>nul
  if errorlevel 1 (
    >>"%LOG%" echo ERROR: Python was not found in PATH.
    >>"%LOG%" echo Install Python from https://www.python.org/downloads/ ^(check "Add python.exe to PATH"^).
    echo Python was not found. See run_app.log
    start "" notepad "%LOG%"
    pause
    exit /b 9009
  ) else (
    set PY_CMD=py -3
  )
)

>>"%LOG%" echo Python cmd: %PY_CMD%
>>"%LOG%" echo --------------------------------------------------
>>"%LOG%" echo.

rem ---- Create venv if missing ----
if not exist "%VENV_DIR%\Scripts\python.exe" (
  >>"%LOG%" echo Creating virtual environment...
  call %PY_CMD% -m venv "%VENV_DIR%" >>"%LOG%" 2>&1
  if errorlevel 1 goto :FAIL
)

set PYV="%VENV_DIR%\Scripts\python.exe"

>>"%LOG%" echo Upgrading pip...
call %PYV% -m pip install -U pip >>"%LOG%" 2>&1
if errorlevel 1 goto :FAIL

>>"%LOG%" echo Installing requirements...
call %PYV% -m pip install -r "%WORKDIR%requirements.txt" >>"%LOG%" 2>&1
if errorlevel 1 goto :FAIL

REM Optional external guardian (separate process) that can attempt a broker-side
REM panic close if the GUI/engine dies while positions are open.
if "%RELENTLESS_GUARDIAN%"=="" set "RELENTLESS_GUARDIAN=1"
if "%RELENTLESS_GUARDIAN%"=="1" (
  start "RelentlessGuardian" /min %PYV% "%WORKDIR%tools\guardian\guardian.py"
  >>"%LOG%" echo Guardian: enabled (tools\guardian\guardian.py)
) else (
  >>"%LOG%" echo Guardian: disabled (set RELENTLESS_GUARDIAN=0)
)

>>"%LOG%" echo Launching GUI...
call %PYV% "%WORKDIR%%SCRIPT%" >>"%LOG%" 2>&1

set EXITCODE=%ERRORLEVEL%
>>"%LOG%" echo --------------------------------------------------
>>"%LOG%" echo ExitCode: %EXITCODE%
if not "%EXITCODE%"=="0" goto :FAIL
exit /b 0

:FAIL
echo.
echo RUN_APP failed (exit code %ERRORLEVEL%).
echo Opening log...
echo.
start "" notepad "%LOG%"
pause
exit /b 1
