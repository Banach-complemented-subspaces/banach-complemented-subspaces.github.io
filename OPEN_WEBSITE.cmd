@echo off
setlocal
cd /d "%~dp0"
set "COMPANION_NODE=%USERPROFILE%\.cache\codex-runtimes\codex-primary-runtime\dependencies\node\bin\node.exe"
if exist "%COMPANION_NODE%" (
  "%COMPANION_NODE%" scripts\open.mjs
) else (
  node scripts\open.mjs
)
if errorlevel 1 pause
