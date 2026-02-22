@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
setlocal EnableExtensions EnableDelayedExpansion
cd /d "%~dp0"

set "LOG=%~dp0run_app.log"
echo -------------------------------------------------->>"%LOG%"
echo INSTALL_DEPS started: %DATE% %TIME%>>"%LOG%"

REM Use system python to create venv if needed
where python >nul 2>&1
if not "%ERRORLEVEL%"=="0" (
  echo ERROR: System Python not found. Install Python and enable PATH.>>"%LOG%"
  echo ERROR: System Python not found. Install Python and enable PATH.
  exit /b 1
)

if not exist "%~dp0.venv\Scripts\python.exe" (
  echo Creating venv...>>"%LOG%"
  python -m venv "%~dp0.venv" 1>>"%LOG%" 2>>"%LOG%"
  if not "%ERRORLEVEL%"=="0" (
    echo ERROR: Failed to create venv.>>"%LOG%"
    exit /b 1
  )
)

set "PY=%~dp0.venv\Scripts\python.exe"

echo Upgrading pip...>>"%LOG%"
"%PY%" -m pip install --upgrade pip 1>>"%LOG%" 2>>"%LOG%"

if not exist "%~dp0requirements.txt" (
  echo ERROR: requirements.txt not found.>>"%LOG%"
  exit /b 1
)

echo Installing requirements...>>"%LOG%"
"%PY%" -m pip install -r "%~dp0requirements.txt" 1>>"%LOG%" 2>>"%LOG%"
if not "%ERRORLEVEL%"=="0" (
  echo ERROR: pip install failed.>>"%LOG%"
  exit /b 1
)

echo INSTALL_DEPS done.>>"%LOG%"
exit /b 0
