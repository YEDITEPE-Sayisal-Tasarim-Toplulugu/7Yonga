
@echo off
cls

set PROGRAMMING_BAUDE_RATE=115200
set PROGRAMMING_DELAY=0
set CORE_CLK_FREQ=50

SET RV_MODE=rv32imaf
SET MABI_MODE=ilp32
SET ELF_MODE=elf32lriscv

SET BOOT_FILE=boot
SET LINKER_FILE=linker

set "DIR=%~dp0"

SET SYSTEM_DIR=%DIR%system
SET APPS_DIR=%DIR%app
SET LIBS_HEADER=%DIR%..\clibs\inc
SET LIBS_SRC_DIR=%DIR%..\clibs\src
SET LIBS_A_DIR=%DIR%..\clibs\a
SET ENV_DIR=%DIR%env
SET BOOT_DIR=%DIR%boot
SET TOOLS_DIR=%cd%\..\..\tools

if not exist "%BOOT_DIR%" (
    mkdir "%BOOT_DIR%"
    echo Folder created: %BOOT_DIR%
)

SET C_FLAGS=-march=%RV_MODE% -mabi=%MABI_MODE% -DCLOCK_FREQ=%CORE_CLK_FREQ% -Wall -O2 -nostdlib -nostartfiles -ffreestanding -I%LIBS_HEADER% -I%APPS_DIR% -T %SYSTEM_DIR%\%LINKER_FILE%.ld

echo:
echo C-Source Compiler v1.1

echo:
echo compile: %BOOT_FILE%.s
riscv64-unknown-elf-as -march=%RV_MODE% -mabi=%MABI_MODE% %SYSTEM_DIR%\%BOOT_FILE%.s -o %SYSTEM_DIR%\%BOOT_FILE%.o

echo:
echo compile: system
for %%i in (%SYSTEM_DIR%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %SYSTEM_DIR%\%%~ni.o
)

echo:
echo compile: app
for %%i in (%APPS_DIR%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %APPS_DIR%\%%~ni.o
)

echo:
echo compile: libs
call %DIR%..\clibs\run.bat

echo create elf file
riscv64-unknown-elf-ld %SYSTEM_DIR%\%BOOT_FILE%.o %SYSTEM_DIR%\init.o %SYSTEM_DIR%\main.o ^
                                %APPS_DIR%\games.o ^
                                %APPS_DIR%\donut.o ^
                                %LIBS_A_DIR%\flib.a ^
                                -T %SYSTEM_DIR%\%LINKER_FILE%.ld -m %ELF_MODE% -o %BOOT_DIR%\boot.elf

for %%F in ("%LIBS_SRC_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%SYSTEM_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%APPS_DIR%\*.o") do (
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
python %TOOLS_DIR%\teknofest_hexdump.py --hexd %BOOT_DIR%/boot_baremetal.mem --bin %BOOT_DIR%/boot.bin
python %TOOLS_DIR%\teknofest_uart_programmer_v1.py --file %BOOT_DIR%/boot.hexd --port COM4 --brate %PROGRAMMING_BAUDE_RATE% --delay %PROGRAMMING_DELAY%
