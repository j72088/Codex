@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
setlocal
cd /d "%~dp0"
set SCRIPT=
for /f "delims=" %%F in ('dir /b /o-n relentless_qt_gui_*.py 2^>nul') do (set SCRIPT=%%F & goto :found)
:found
if "%SCRIPT%"=="" (
  echo Could not find relentless_qt_gui_*.py
  pause
  exit /b 1
)
python "%SCRIPT%" --export-diagnostics --diagnostics-reason manual
pause
endlocal
