@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
REM Legacy alias (idiot-proof): use BUILD_EXE.bat
call "%~dp0BUILD_EXE.bat"
