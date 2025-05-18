@echo off

echo FLIBS COMPILER V1.0

set DIR=%~dp0

SET LIB_NAME=flib

SET RV_MODE=rv32imaf
SET MABI_MODE=ilp32
SET ELF_MODE=elf32lriscv

set COPY_LIB_DIR=%DIR%a
set LIBS_HEADERS=%DIR%inc
set LIBS_SOURCES=%DIR%src

set C_FLAGS=-Wno-unused-but-set-variable -Wno-unused-function -march=%RV_MODE% -mabi=%MABI_MODE% -Wall -O2 -nostdlib -nostartfiles -ffreestanding -I%LIBS_HEADERS%

del %COPY_LIB_DIR%\%LIB_NAME%.a

for %%i in (%LIBS_SOURCES%\*.c) do (
    echo compile: %%i
    riscv64-unknown-elf-gcc %C_FLAGS% -c %%i -o %LIBS_SOURCES%\%%~ni.o
)

riscv64-unknown-elf-ar rcs %LIB_NAME%.a %LIBS_SOURCES%\stdio.o^
                                        %LIBS_SOURCES%\string.o^
                                        %LIBS_SOURCES%\timer.o ^
                                        %LIBS_SOURCES%\uart.o ^
                                        %LIBS_SOURCES%\random.o

copy %LIB_NAME%.a %COPY_LIB_DIR%

rem temizlik
for %%F in ("%LIBS_SOURCES%\*.o") do (
    del "%%F"
)
del %DIR%%LIB_NAME%.a
