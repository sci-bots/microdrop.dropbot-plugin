@echo off
set PLUGIN_NAME=dropbot_plugin

REM Unlink installed plugin from Conda MicroDrop activated plugins directory.
call conda activate "%PREFIX%" & python -m mpm.bin.api disable %PLUGIN_NAME%
echo Unlinked `%PLUGIN_NAME%` from MicroDrop activated plugins directory. > "%PREFIX%\.messages.txt"

REM Disable loading of plugin in MicroDrop.
call conda activate "%PREFIX%" & microdrop-config edit --remove plugins.enabled %PLUGIN_NAME%
echo Disable loading of `%PLUGIN_NAME%` in MicroDrop. >> "%PREFIX%\.messages.txt"
