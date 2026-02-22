@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8

setlocal

cd /d "%~dp0"

echo DEBUG_EXE is for packaged builds. If you are running from source, use RUN_APP.bat.

call RUN_APP.bat

