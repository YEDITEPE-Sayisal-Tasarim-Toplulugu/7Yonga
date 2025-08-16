@echo off
setlocal enabledelayedexpansion

echo ======================================
echo    SystemVerilog Testbench Runner    
echo         Windows - XSIM (Vivado)      
echo ======================================
echo.

REM Check if xvlog is available
where xvlog >nul 2>nul
if %errorlevel% neq 0 (
    echo ERROR: XSIM not found in PATH!
    echo Please run Vivado settings64.bat first or add to PATH
    echo Example: C:\Xilinx\Vivado\2023.2\settings64.bat
    pause
    exit /b 1
)

REM Create directories
if not exist "xsim_work" mkdir xsim_work
if not exist "test_results" mkdir test_results
if not exist "logs" mkdir logs

REM Clean previous results
echo Cleaning previous results...
if exist "xsim.dir" rmdir /s /q xsim.dir
del /q logs\*.log 2>nul
del /q *.jou 2>nul
del /q *.pb 2>nul
del /q *.wdb 2>nul

REM Initialize counters
set /a total_tests=0
set /a passed_tests=0
set /a failed_tests=0

REM Compile all RTL files
echo.
echo Compiling RTL files...
xvlog -sv gpio.sv timer.sv uart.sv qspi_master.sv > logs\rtl_compile.log 2>&1
if %errorlevel% neq 0 (
    echo ERROR: RTL compilation failed!
    echo Check logs\rtl_compile.log for details
    pause
    exit /b 1
)
echo RTL compilation successful!

REM Run tests
echo.
echo Running testbenches...
echo ----------------------

call :run_test gpio_tb gpio
call :run_test timer_tb timer  
call :run_test tb_uart uart
call :run_test qspi_master_tb qspi_master

REM Print summary
echo.
echo ======================================
echo            TEST SUMMARY              
echo ======================================
echo Total tests:  %total_tests%
echo Passed:       %passed_tests%
echo Failed:       %failed_tests%
echo ======================================

if %failed_tests% equ 0 (
    echo.
    echo ALL TESTS PASSED!
    echo.
) else (
    echo.
    echo SOME TESTS FAILED!
    echo Check logs directory for details.
    echo.
)

REM Cleanup
del /q *.jou 2>nul
del /q *.pb 2>nul

pause
exit /b %failed_tests%

:run_test
set tb_name=%1
set module_name=%2
set /a total_tests+=1

echo.
echo [%total_tests%] Testing %module_name%...

REM Compile testbench
xvlog -sv %tb_name%.sv > logs\%module_name%_tb_compile.log 2>&1
if %errorlevel% neq 0 (
    echo    - Compilation: FAILED
    echo    - Check logs\%module_name%_tb_compile.log
    set /a failed_tests+=1
    goto :eof
)
echo    - Compilation: OK

REM Elaborate
xelab -debug typical -top %tb_name% -snapshot %tb_name%_snapshot > logs\%module_name%_elab.log 2>&1
if %errorlevel% neq 0 (
    echo    - Elaboration: FAILED
    echo    - Check logs\%module_name%_elab.log
    set /a failed_tests+=1
    goto :eof
)
echo    - Elaboration: OK

REM Run simulation
echo    - Running simulation...
xsim %tb_name%_snapshot -runall -log logs\%module_name%_sim.log > logs\%module_name%_xsim_output.log 2>&1
if %errorlevel% neq 0 (
    echo    - Simulation:  FAILED (crashed)
    set /a failed_tests+=1
    goto :eof
)

REM Check for test results in simulation log
findstr /C:"Test PASSED" /C:"SUCCESS" /C:"Test BAŞARILI" logs\%module_name%_sim.log >nul
if %errorlevel% equ 0 (
    echo    - Result:      PASSED
    set /a passed_tests+=1
) else (
    findstr /C:"Test FAILED" /C:"ERROR" /C:"Test BAŞARISIZ" logs\%module_name%_sim.log >nul
    if !errorlevel! equ 0 (
        echo    - Result:      FAILED
        set /a failed_tests+=1
    ) else (
        echo    - Result:      UNKNOWN (check log)
        set /a failed_tests+=1
    )
)

REM Copy important results
findstr /C:"Test" /C:"ERROR" /C:"SUCCESS" /C:"FAILED" /C:"BAŞARILI" logs\%module_name%_sim.log > test_results\%module_name%_summary.txt 2>nul

goto :eof