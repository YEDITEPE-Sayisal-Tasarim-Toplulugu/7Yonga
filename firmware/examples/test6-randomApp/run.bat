
@echo off
cls

rem SET MAIN_FILE=pipTest_006
set "MAIN_FILE=%~1"
IF %1.==. GOTO No1

set PROGRAMMING_BAUDE_RATE=115200
set PROGRAMMING_DELAY=0

SET RV_MODE=rv32imb
SET MABI_MODE=ilp32
SET ELF_MODE=elf32lriscv

SET BOOT_FILE=boot
SET LINKER_FILE=linker

set "DIR=%~dp0"

SET SRC_DIR=%DIR%src
SET ENV_DIR=%DIR%env
SET BOOT_DIR=%DIR%boot
SET TOOLS_DIR=%cd%\..\..\tools

if not exist "%BOOT_DIR%" (
    mkdir "%BOOT_DIR%"
    echo Folder created: %BOOT_DIR%
)

SET C_FLAGS=-march=%RV_MODE% -mabi=%MABI_MODE% -Wall -O2 -nostdlib -nostartfiles -ffreestanding -T %ENV_DIR%\%LINKER_FILE%.ld

echo:
echo C-Source Compiler v1.1

echo:
echo compile: %BOOT_FILE%.s
riscv64-unknown-elf-as -march=%RV_MODE% -mabi=%MABI_MODE% -Ienv/ %ENV_DIR%\%BOOT_FILE%.s -o %ENV_DIR%\%BOOT_FILE%.o

echo compile: %MAIN_FILE%.c
riscv64-unknown-elf-gcc %C_FLAGS% -c %SRC_DIR%\%MAIN_FILE%.c -o %SRC_DIR%/%MAIN_FILE%.o

echo create elf file
riscv64-unknown-elf-ld %ENV_DIR%\%BOOT_FILE%.o %SRC_DIR%\%MAIN_FILE%.o -T %ENV_DIR%\%LINKER_FILE%.ld -m %ELF_MODE% -o %BOOT_DIR%\boot.elf

for %%F in ("%ENV_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%SRC_DIR%\*.o") do (
    del "%%F"
)
echo .o files have been removed.

echo create hex file
riscv64-unknown-elf-objcopy -O ihex %BOOT_DIR%/boot.elf %BOOT_DIR%/boot.hex

echo create list file
riscv64-unknown-elf-objdump -M no-aliases -D %BOOT_DIR%/boot.elf > %BOOT_DIR%/boot.list

echo create binary file
riscv64-unknown-elf-objcopy -O binary %BOOT_DIR%/boot.elf %BOOT_DIR%/boot.bin
echo:
python %TOOLS_DIR%\teknofest_hexdump.py --hexd %BOOT_DIR%/boot.hexd --bin %BOOT_DIR%/boot.bin
python %TOOLS_DIR%\teknofest_hexdump.py --hexd %BOOT_DIR%/boot_app.mem --bin %BOOT_DIR%/boot.bin
python %TOOLS_DIR%\teknofest_uart_programmer_v1.py --file %BOOT_DIR%/boot.hexd --port COM4 --brate %PROGRAMMING_BAUDE_RATE% --delay %PROGRAMMING_DELAY%

:No1
echo ERROR: file_name?
:No2