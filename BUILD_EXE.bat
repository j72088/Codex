@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8

setlocal

cd /d "%~dp0"

echo BUILD_EXE is not included in this debug-only builder zip.

echo If you need a packaged EXE build, use the builder workflow under tools\internal\_DO_NOT_OPEN_build_windows_exe.ps1

pause

