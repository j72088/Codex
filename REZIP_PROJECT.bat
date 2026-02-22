@echo off
setlocal ENABLEEXTENSIONS
cd /d "%~dp0"

set "OUT=RelentlessExecution_update_%DATE:~10,4%%DATE:~4,2%%DATE:~7,2%_%TIME:~0,2%%TIME:~3,2%%TIME:~6,2%.zip"
set "OUT=%OUT: =0%"

powershell -NoProfile -Command "Compress-Archive -Path @('*.py','*.txt','*.bat','requirements.txt') -DestinationPath '%OUT%' -Force"
if errorlevel 1 (
  echo Failed to create zip.
  exit /b 1
)

echo Created: %CD%\%OUT%
exit /b 0
