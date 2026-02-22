@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8

setlocal

cd /d "%~dp0"

call RUN_APP.bat

