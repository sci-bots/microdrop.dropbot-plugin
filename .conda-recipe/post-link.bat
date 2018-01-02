@echo off
set PLUGIN_NAME=dropbot_plugin

REM Link installed plugin into Conda MicroDrop activated plugins directory.
call "%PREFIX%\Scripts\activate.bat" "%PREFIX%" & python -m mpm.bin.api enable %PLUGIN_NAME%
echo Linked `%PLUGIN_NAME%` into MicroDrop activated plugins directory. > "%PREFIX%\.messages.txt"

REM Load plugin by default
call "%PREFIX%\Scripts\activate.bat" "%PREFIX%" & microdrop-config edit --append plugins.enabled %PLUGIN_NAME%
echo Configured MicroDrop to load `%PLUGIN_NAME%` by default. >> "%PREFIX%\.messages.txt"
