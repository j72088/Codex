@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
setlocal
cd /d "%~dp0"

set "SCRIPT="

REM Pick newest script by semantic version (avoids _10 vs _9 lexicographic traps)
for /f "usebackq delims=" %%F in (`powershell -NoProfile -Command "Get-ChildItem -File -Filter 'relentless_qt_gui_v*.py' | ForEach-Object { $b=$_.BaseName -replace '^relentless_qt_gui_v',''; $v=$b -replace '_','.'; try{$ver=[version]$v}catch{$ver=[version]'0.0.0'}; [pscustomobject]@{Name=$_.Name;Ver=$ver} } | Sort-Object Ver -Descending | Select-Object -First 1 -ExpandProperty Name"`) do (
  set "SCRIPT=%%F"
)

if "%SCRIPT%"=="" (
  echo Could not find relentless_qt_gui_v*.py
  pause
  exit /b 1
)

python "%SCRIPT%" --self-test
pause
endlocal
