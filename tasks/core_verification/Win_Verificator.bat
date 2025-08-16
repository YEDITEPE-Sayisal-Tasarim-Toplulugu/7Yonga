@echo off
REM 7Yonga
REM Yeditepe Üniversitesi, Sayısal Tasarım Topluluğu
REM 06.2025

SET OUT_DIR=%cd%\OUT
SET VIVADO_DIR=D:\Programlar\VIVADOLIC\Vivado\2024.1

if not exist %OUT_DIR% (
    mkdir %OUT_DIR%
)

REM Batch script for generating file list and running Vivado in batch mode

REM Ortam değişkenlerini ayarla (Vivado için)
call "%VIVADO_DIR%\settings64.bat"

REM Geçerli dizini kaydet
set CURRENT_DIR=%~dp0
REM Sonunda ters eğik çizgi varsa sil
if "%CURRENT_DIR:~-1%"=="\" set CURRENT_DIR=%CURRENT_DIR:~0,-1%

REM Python scriptini çalıştır
python.exe .\freelist_generator_v2.py --i files.txt --o %OUT_DIR%\files.f --b %CURRENT_DIR%\..\..\

for %%F in ("*.backup.log") do (
    del "%%F"
)
for %%F in ("*.backup.jou") do (
    del "%%F"
)

REM Vivado'yu batch modda çalıştır
vivado -mode batch -source verification.tcl

ECHO BYE!
