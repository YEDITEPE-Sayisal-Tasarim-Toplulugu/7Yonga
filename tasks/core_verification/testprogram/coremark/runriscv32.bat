@echo off

SET RV_MODE=rv32im
SET MABI_MODE=ilp32
SET ELF_MODE=elf32lriscv

SET COREMARK_DIR=%cd%\coremark
SET PORT_DIR=%cd%\port
SET LIBS_DIR=%cd%\libs
SET BOOT_DIR=%cd%\OUT
SET TOOLS_DIR=%cd%\tools

SET BOOT_FILE=boot
SET LINKER_FILE=linker
SET MAIN_FILE=notmain-riscv

set PROGRAMMING_BAUDE_RATE=115200
set PROGRAMMING_DELAY=0

SET CORE_DEBUG=1
SET ITERATIONS=1
SET CLOCK_RATE=50

SET C_FLAGS=-march=%RV_MODE% -mabi=%MABI_MODE% -I%PORT_DIR% -I%COREMARK_DIR% -I%LIBS_DIR% -DCORE_DEBUG=%CORE_DEBUG% -DITERATIONS=%ITERATIONS% -DCPU_CLOCK_FREQUENCY=%CLOCK_RATE% -Wall -O2 -nostdlib -nostartfiles -ffreestanding -T %LINKER_FILE%.ld

echo:
echo CoreMark Compiler v3.0

if not exist %BOOT_DIR% (
    mkdir %BOOT_DIR%
)


echo:
echo compile: %BOOT_FILE%.s
riscv64-unknown-elf-as -march=%RV_MODE% -mabi=%MABI_MODE% %BOOT_FILE%.s -o %BOOT_FILE%.o

echo:
echo compile: %MAIN_FILE%.c
riscv64-unknown-elf-gcc %C_FLAGS% -c %MAIN_FILE%.c -o %MAIN_FILE%.o

for %%i in (%LIBS_DIR%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %LIBS_DIR%\%%~ni.o
)

for %%i in (%PORT_DIR%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %PORT_DIR%\%%~ni.o
)

for %%i in (%COREMARK_DIR%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %COREMARK_DIR%\%%~ni.o
)

echo:
echo create elf file
riscv64-unknown-elf-ld %BOOT_FILE%.o %MAIN_FILE%.o ^
                                    %LIBS_DIR%\uart_driver.o ^
                                    %LIBS_DIR%\timer.o ^
                                    %LIBS_DIR%\string.o ^
                                    %LIBS_DIR%\stdio.o ^
                                    %PORT_DIR%\core_portme.o ^
                                    %COREMARK_DIR%\core_main.o ^
                                    %COREMARK_DIR%\core_util.o ^
                                    %COREMARK_DIR%\core_state.o ^
                                    %COREMARK_DIR%\core_matrix.o ^
                                    %COREMARK_DIR%\core_list_join.o ^
                                    -T %LINKER_FILE%.ld -m %ELF_MODE% -o %BOOT_DIR%\boot.elf

for %%F in ("%LIBS_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%PORT_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%COREMARK_DIR%\*.o") do (
    del "%%F"
)
for %%F in ("%cd%\*.o") do (
    del "%%F"
)
echo:
echo .o files have been removed.

echo:
echo create hex file
riscv64-unknown-elf-objcopy -O ihex %BOOT_DIR%/boot.elf %BOOT_DIR%/boot.hex

echo:
echo create list file
riscv64-unknown-elf-objdump -M no-aliases -D %BOOT_DIR%/boot.elf > %BOOT_DIR%/boot.list

echo:
echo create binary file
riscv64-unknown-elf-objcopy -O binary %BOOT_DIR%/boot.elf %BOOT_DIR%/boot.bin

echo:
echo program upload

echo:
echo Constants:
echo CORE_DEBUG = %CORE_DEBUG%
echo ITERATIONS = %ITERATIONS%
echo CLOCK_RATE = %CLOCK_RATE% MHz
echo:

python riscv_tool_hexdump.py --o %BOOT_DIR%/program.mem --bin %BOOT_DIR%/boot.bin

