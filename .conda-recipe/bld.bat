@echo off
setlocal enableextensions
md "%PREFIX%"\share\microdrop\available
endlocal
xcopy /S /Y /I /Q "%SRC_DIR%" "%PREFIX%"\share\microdrop\available\"%PKG_NAME%"
if errorlevel 1 exit 1
