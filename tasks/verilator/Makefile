# M. Furkan UZUN

BASE_DIR		:= $(realpath ../../)

TOP_MODULE     	:= tb_verilator
BUILD_DIR      	:= build
OBJ_DIR        	:= obj_dir
EXECUTABLE     	:= $(BUILD_DIR)/sim.out

SV_FILES 		+= $(wildcard $(BASE_DIR)/tasks/boot_steps/OUT/boot_code.sv)

VERILATOR_OPTS 	:= -Wall -cc --trace --timing -j 0  --coverage --trace-fst --hierarchical

PARAMETERS		+= -DVERILATOR=1

VERILATOR_IGONRE	+= -Wno-DECLFILENAME
VERILATOR_IGONRE	+= -Wno-VARHIDDEN
VERILATOR_IGONRE	+= -Wno-GENUNNAMED
VERILATOR_IGONRE	+= -Wno-BLKSEQ
VERILATOR_IGONRE	+= -Wno-UNUSEDPARAM
VERILATOR_IGONRE	+= -Wno-UNUSEDSIGNAL
VERILATOR_IGONRE	+= -Wno-TIMESCALEMOD
VERILATOR_IGONRE	+= -Wno-PINCONNECTEMPTY
VERILATOR_IGONRE	+= -Wno-EOFNEWLINE
VERILATOR_IGONRE	+= -Wno-IMPORTSTAR
VERILATOR_IGONRE	+= -Wno-CASEINCOMPLETE
VERILATOR_IGONRE	+= -Wno-UNDRIVEN
VERILATOR_IGONRE	+= -Wno-WIDTHEXPAND
VERILATOR_IGONRE	+= -Wno-UNSIGNED
VERILATOR_IGONRE	+= -Wno-WIDTHTRUNC
VERILATOR_IGONRE	+= -Wno-ASCRANGE

VERILATOR_FLAGS = $(VERILATOR_OPTS) $(PARAMETERS) $(INCLUDE_DIRS) $(VERILATOR_IGONRE)

all: $(EXECUTABLE)

$(EXECUTABLE): $(SV_FILES)
	verilator $(VERILATOR_FLAGS) --binary -o sim.out --Mdir $(OBJ_DIR) \
		--top-module $(TOP_MODULE) $(SV_FILES)
	make -C $(OBJ_DIR) -f V$(TOP_MODULE).mk

	@mkdir -p $(BUILD_DIR)
	@cp $(OBJ_DIR)/sim.out $(EXECUTABLE)

linter: $(SV_FILES) | $(RESULT_DIR)
	verilator $(VERILATOR_FLAGS) --lint-only -o sim.out \
		--top-module $(TOP_MODULE) $(SV_FILES)

build: $(EXECUTABLE)
	@echo "Build Completed..."

run: all
	./$(EXECUTABLE)

# Temizlik
clean:
	rm -rf $(OBJ_DIR) $(BUILD_DIR)

.PHONY: all clean run

include sources.mk
