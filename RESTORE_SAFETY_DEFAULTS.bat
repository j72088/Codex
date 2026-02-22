@echo off
chcp 65001 >nul
set PYTHONUTF8=1
set PYTHONIOENCODING=utf-8
echo Restore safety defaults: Open %%APPDATA%%\RelentlessExecution\settings.json and set "paper_relax": false
pause
