REPO_URL := https://github.com/openhwgroup/cv32e40p.git
REPO_DIR := $(pwd)

TESTSUIT_DIR = testsuit
CORE_DIR = cv32e40p
BUILD_DIR=build

OBJ_DIR = obj

PKG = -DVERILATOR=1
# PKG = -DUVM_DEBUG=1
# PKG += -DCV32E40P_ASSERT_ON=1
# PKG += -DCV32E40P_CORE_LOG=1
# PKG += -DCV32E40P_APU_TRACE=1
# PKG += -DCV32E40P_TRACE_EXECUTION=1
# PKG += -DCV32E40P_RVFI=1
# PKG += -DCV32E40P_RVFI_TRACE_EXECUTION=1

TOP_MODULE=tb_suit

HEADER_FILE=
VERILOG_FILE=

HEADER_FILE += -I$(TESTSUIT_DIR)/
HEADER_FILE += -I$(TESTSUIT_DIR)/inc/
HEADER_FILE += -I$(CORE_DIR)/rtl/include/
HEADER_FILE += -I$(CORE_DIR)/rtl/vendor/pulp_platform_fpnew/src/
HEADER_FILE += -I$(CORE_DIR)/rtl/vendor/pulp_platform_common_cells/src/
HEADER_FILE += -I$(CORE_DIR)/rtl/vendor/pulp_platform_common_cells/include/
HEADER_FILE += -I$(CORE_DIR)/rtl/vendor/pulp_platform_common_cells/include/common_cells/

VERILOG_FILE += $(TESTSUIT_DIR)/inc/*.sv
VERILOG_FILE += $(TESTSUIT_DIR)/*.sv
VERILOG_FILE += $(TESTSUIT_DIR)/memory_system/*.sv

VERILOG_FILE += $(CORE_DIR)/rtl/vendor/pulp_platform_common_cells/src/*.sv
VERILOG_FILE += $(CORE_DIR)/rtl/vendor/pulp_platform_common_cells/src/deprecated/*.sv
VERILOG_FILE += $(CORE_DIR)/rtl/include/*.sv
VERILOG_FILE += $(CORE_DIR)/rtl/vendor/pulp_platform_fpnew/src/fpnew_pkg.sv
VERILOG_FILE += $(CORE_DIR)/rtl/vendor/pulp_platform_fpnew/src/*.sv
VERILOG_FILE += $(CORE_DIR)/rtl/*.sv

IGNORING_WARNING_LIST = -Wno-BLKANDNBLK
IGNORING_WARNING_LIST += -Wno-UNOPTFLAT
IGNORING_WARNING_LIST += -Wno-REALCVT
IGNORING_WARNING_LIST += -Wno-WIDTHTRUNC
IGNORING_WARNING_LIST += -Wno-LATCH
IGNORING_WARNING_LIST += -Wno-CASEINCOMPLETE
IGNORING_WARNING_LIST += -Wno-WIDTHEXPAND
IGNORING_WARNING_LIST += -Wno-ASCRANGE
IGNORING_WARNING_LIST += -Wno-MODDUP
IGNORING_WARNING_LIST += -Wno-PINMISSING
IGNORING_WARNING_LIST += -Wno-COMBDLY

.PHONY: setup build run clean

setup:
	@if [ ! -d "$(REPO_DIR)" ]; then \
		git clone $(REPO_URL); \
	else \
		echo "$(REPO_DIR) already exists. Skipping clone."; \
	fi

all: build

$(OBJ_DIR):
	mkdir $(OBJ_DIR)

$(OBJ_DIR)/files.f: $(OBJ_DIR) $(VERILOG_FILE)
	echo FILES: $(VERILOG_FILE)
	echo $(VERILOG_FILE) > $(OBJ_DIR)/files_temp.f
	python3 freelist_generator.py --i $(OBJ_DIR)/files_temp.f --o $(OBJ_DIR)/files.f

build: $(OBJ_DIR)/files.f
	verilator $(IGNORING_WARNING_LIST) $(PKG) --cc --sv --binary $(HEADER_FILE) -o simv --top-module $(TOP_MODULE) -f $(OBJ_DIR)/files.f && cp $(OBJ_DIR)/simv $(BUILD_DIR)/simv

run:
	$(BUILD_DIR)/simv

clean:
	rm -rf $(BUILD_DIR) $(OBJ_DIR)
