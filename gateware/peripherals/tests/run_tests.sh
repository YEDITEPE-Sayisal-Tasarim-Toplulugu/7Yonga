#!/bin/bash

echo "======================================"
echo "   SystemVerilog Testbench Runner    "
echo "        Linux - ModelSim/IVerilog    "
echo "======================================"
echo

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Detect available simulator
SIMULATOR=""
if command -v vsim &> /dev/null; then
    SIMULATOR="modelsim"
    echo -e "${GREEN}Found ModelSim${NC}"
elif command -v iverilog &> /dev/null; then
    SIMULATOR="iverilog"
    echo -e "${GREEN}Found Icarus Verilog${NC}"
else
    echo -e "${RED}ERROR: No simulator found!${NC}"
    echo "Please install ModelSim or Icarus Verilog:"
    echo "  sudo apt-get install iverilog"
    exit 1
fi

# Create directories
mkdir -p work test_results logs

# Clean previous results
rm -f logs/*.log

# Initialize counters
total_tests=0
passed_tests=0
failed_tests=0

# Function to run test with ModelSim
run_modelsim_test() {
    local tb_name=$1
    local module_name=$2
    
    # Compile testbench
    vlog -sv ${tb_name}.sv > logs/${module_name}_tb_compile.log 2>&1
    if [ $? -ne 0 ]; then
        echo -e "   - Compilation: ${RED}FAILED${NC}"
        echo "   - Check logs/${module_name}_tb_compile.log"
        ((failed_tests++))
        return 1
    fi
    echo -e "   - Compilation: ${GREEN}OK${NC}"
    
    # Run simulation
    vsim -c -do "run -all; quit" work.${tb_name} > logs/${module_name}_sim.log 2>&1
    if [ $? -ne 0 ]; then
        echo -e "   - Simulation:  ${RED}FAILED (crashed)${NC}"
        ((failed_tests++))
        return 1
    fi
    
    # Check results
    if grep -q "Test PASSED\|SUCCESS" logs/${module_name}_sim.log; then
        echo -e "   - Simulation:  ${GREEN}PASSED${NC}"
        echo -e "   - Result:      ${GREEN}SUCCESS${NC}"
        ((passed_tests++))
        return 0
    elif grep -q "Test FAILED\|ERROR" logs/${module_name}_sim.log; then
        echo -e "   - Simulation:  ${YELLOW}COMPLETED${NC}"
        echo -e "   - Result:      ${RED}FAILED${NC}"
        ((failed_tests++))
        return 1
    else
        echo -e "   - Simulation:  ${YELLOW}COMPLETED${NC}"
        echo -e "   - Result:      ${YELLOW}UNKNOWN${NC} (check log)"
        ((failed_tests++))
        return 1
    fi
}

# Function to run test with Icarus Verilog
run_iverilog_test() {
    local tb_name=$1
    local module_name=$2
    
    # Compile
    iverilog -g2012 -o work/${tb_name}.vvp ${module_name}.sv ${tb_name}.sv > logs/${module_name}_compile.log 2>&1
    if [ $? -ne 0 ]; then
        echo -e "   - Compilation: ${RED}FAILED${NC}"
        echo "   - Check logs/${module_name}_compile.log"
        ((failed_tests++))
        return 1
    fi
    echo -e "   - Compilation: ${GREEN}OK${NC}"
    
    # Run simulation
    vvp work/${tb_name}.vvp > logs/${module_name}_sim.log 2>&1
    if [ $? -ne 0 ]; then
        echo -e "   - Simulation:  ${RED}FAILED (crashed)${NC}"
        ((failed_tests++))
        return 1
    fi
    
    # Check results (same as ModelSim)
    if grep -q "Test PASSED\|SUCCESS" logs/${module_name}_sim.log; then
        echo -e "   - Simulation:  ${GREEN}PASSED${NC}"
        echo -e "   - Result:      ${GREEN}SUCCESS${NC}"
        ((passed_tests++))
        return 0
    elif grep -q "Test FAILED\|ERROR" logs/${module_name}_sim.log; then
        echo -e "   - Simulation:  ${YELLOW}COMPLETED${NC}"
        echo -e "   - Result:      ${RED}FAILED${NC}"
        ((failed_tests++))
        return 1
    else
        echo -e "   - Simulation:  ${YELLOW}COMPLETED${NC}"
        echo -e "   - Result:      ${YELLOW}UNKNOWN${NC} (check log)"
        ((failed_tests++))
        return 1
    fi
}

# Compile RTL files first
echo
echo "Compiling RTL files..."

if [ "$SIMULATOR" = "modelsim" ]; then
    vlib work > /dev/null 2>&1
    vlog -sv gpio.sv timer.sv uart.sv qspi_master.sv > logs/rtl_compile.log 2>&1
else
    # For iverilog, we compile with each testbench
    echo "RTL files will be compiled with testbenches"
fi

if [ $? -ne 0 ] && [ "$SIMULATOR" = "modelsim" ]; then
    echo -e "${RED}ERROR: RTL compilation failed!${NC}"
    echo "Check logs/rtl_compile.log for details"
    exit 1
fi
echo -e "${GREEN}RTL compilation successful!${NC}"

# Test list
declare -a tests=(
    "gpio_tb:gpio"
    "timer_tb:timer"
    "tb_uart:uart"
    "qspi_master_tb:qspi_master"
)

# Run all tests
echo
echo "Running testbenches..."
echo "----------------------"

for test in "${tests[@]}"; do
    IFS=':' read -r tb_name module_name <<< "$test"
    ((total_tests++))
    
    echo
    echo -e "${BLUE}[$total_tests] Testing $module_name...${NC}"
    
    if [ "$SIMULATOR" = "modelsim" ]; then
        run_modelsim_test $tb_name $module_name
    else
        run_iverilog_test $tb_name $module_name
    fi
    
    # Extract summary
    grep -E "Test|ERROR|SUCCESS|FAILED" logs/${module_name}_sim.log > test_results/${module_name}_summary.txt 2>/dev/null
done

# Print summary
echo
echo "======================================"
echo "           TEST SUMMARY              "
echo "======================================"
echo -e "Total tests:  $total_tests"
echo -e "Passed:       ${GREEN}$passed_tests${NC}"
echo -e "Failed:       ${RED}$failed_tests${NC}"
echo "======================================"

if [ $failed_tests -eq 0 ]; then
    echo
    echo -e "${GREEN}ALL TESTS PASSED!${NC}"
    echo
    exit 0
else
    echo
    echo -e "${RED}SOME TESTS FAILED!${NC}"
    echo "Check logs directory for details."
    echo
    exit 1
fi