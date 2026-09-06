@echo off
setlocal
cd /d "%~dp0"
set "COMPANION_NODE=%USERPROFILE%\.cache\codex-runtimes\codex-primary-runtime\dependencies\node\bin\node.exe"
if exist "%COMPANION_NODE%" (
  "%COMPANION_NODE%" scripts\build.mjs
) else (
  node scripts\build.mjs
)
if errorlevel 1 pause
