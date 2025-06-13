@echo off
rem ============================================================
rem  SystemVerilog Testbench Runner – Windows (ModelSim / XSIM)
rem ============================================================
rem  Gereken dizinler
if not exist logs           md logs
if not exist work           md work
if not exist test_results   md test_results

rem ------------------------------------------------------------
rem  Renk kodları (Windows 10+  ANSI destekli)
for /f "delims=" %%A in ('echo prompt $E^| cmd') do set "ESC=%%A"
set "RED=%ESC%[31m"
set "GREEN=%ESC%[32m"
set "YEL=%ESC%[33m"
set "BLU=%ESC%[34m"
set "RST=%ESC%[0m"

echo(
echo   %BLU%======================================%RST%
echo   %BLU%  Windows Testbench Runner           %RST%
echo   %BLU%======================================%RST%
echo(

rem ------------------------------------------------------------
rem  Simülatör algılama
set SIM=
where vsim    >nul 2>nul && set SIM=modelsim
where xvlog   >nul 2>nul && where xsim >nul 2>nul && set SIM=xsim

if not defined SIM (
    echo %RED%ERROR:%RST% Uygun bir simülatör bulunamadı^!
    echo ModelSim yükleyin **veya** Vivado "Tcl Shell" te çalıştırın.
    exit /b 1
)
echo %GREEN%Found %SIM%%RST%
echo(

rem ------------------------------------------------------------
rem  Ortak ayarlar
set RTL=gpio.sv timer.sv uart.sv qspi_master.sv
set TESTS=gpio_tb:gpio timer_tb:timer tb_uart:uart qspi_master_tb:qspi_master

rem ============================================================
rem  MODEL SIM  ------------------------------------------------
if "%SIM%"=="modelsim" (
    echo %BLU%--- RTL derleniyor (ModelSim)...%RST%
    vlib work
    vlog -sv %RTL% > logs\rtl_compile.log 2>&1 || goto :fatal_rtl

    for %%T in (%TESTS%) do (
        for /f "tokens=1,2 delims=:" %%a in ("%%T") do (
            call :run_msim %%a %%b
        )
    )
    goto :summary
)

rem ============================================================
rem  XSIM  -----------------------------------------------------
:run_xsim_all
echo %BLU%--- Testler XSIM ile koşturuluyor...%RST%
for %%T in (%TESTS%) do (
    for /f "tokens=1,2 delims=:" %%a in ("%%T") do (
        call :run_xsim %%a %%b
    )
)
goto :summary

rem ============================================================
rem  ----- alt yordamlar --------------------------------------
:run_msim
set TB=%1
set MOD=%2
echo %BLU%[%%TB%%] %MOD%%RST%
vlog -sv %%TB%%.sv > logs\%%MOD%%_tb_compile.log 2>&1 || (
    echo   - Compile %RED%FAILED%RST%
    goto :fail
)
vsim -c -do "run -all; quit" work.%%TB%% > logs\%%MOD%%_sim.log 2>&1
findstr /C:"Test PASSED" /C:"SUCCESS" logs\%%MOD%%_sim.log >nul && (
    echo   - Result %GREEN%PASSED%RST%
    set /a PASS+=1
    goto :eof
)
echo   - Result %RED%FAILED%RST%
set /a FAIL+=1
goto :eof

:run_xsim
set TB=%1
set MOD=%2
echo %BLU%[%%TB%%] %MOD%%RST%
xvlog -sv %%MOD%%.sv %%TB%%.sv > logs\%%MOD%%_compile.log 2>&1 || (
    echo   - Compile %RED%FAILED%RST%
    goto :fail
)
xelab work.%%TB%% > nul 2>&1 || goto :fail
xsim   work.%%TB%% -R --runall > logs\%%MOD%%_sim.log 2>&1
findstr /C:"Test PASSED" /C:"SUCCESS" logs\%%MOD%%_sim.log >nul && (
    echo   - Result %GREEN%PASSED%RST%
    set /a PASS+=1
    goto :eof
)
echo   - Result %RED%FAILED%RST%
set /a FAIL+=1
goto :eof

:fatal_rtl
echo %RED%RTL derleme hatası – logs\rtl_compile.log dosyasına bak%RST%
exit /b 1

:summary
set /a TOTAL=%PASS%+%FAIL%
echo(
echo %BLU%============ TEST SUMMARY ============%RST%
echo   Toplam : %TOTAL%
echo   Geçen  : %GREEN%%PASS%%RST%
echo   Kalan  : %RED%%FAIL%%RST%
echo %BLU%======================================%RST%
exit /b 0

:fail
set /a FAIL+=1
goto :eof
