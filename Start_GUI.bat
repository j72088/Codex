@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8

REM Legacy alias (idiot-proof): use RUN_APP.bat

call "%~dp0RUN_APP.bat"

