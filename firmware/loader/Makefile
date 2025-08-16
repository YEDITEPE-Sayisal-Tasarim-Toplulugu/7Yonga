# RISC-V toolchain prefix
CROSS_COMPILE = riscv64-unknown-elf-

AS      		= $(CROSS_COMPILE)as
CC      		= $(CROSS_COMPILE)gcc
LD      		= $(CROSS_COMPILE)ld
OBJDUMP 		= $(CROSS_COMPILE)objdump
OBJCOPY 		= $(CROSS_COMPILE)objcopy
PY_BIN_PARSER	?= ../riscv_tool_hexdump.py

# Architecture settings
RV_MODE   		= rv32i
MABI_MODE 		= ilp32

# Project settings
BUILD_DIR 		?= BUILD
OBJ_DIR 		?= OBJ
TARGET  		= $(BUILD_DIR)/program
SRC_DIR 		= SRC
LINKER_SCRIPT 	= linker.ld

# Source files (hem .s hem .c)
SRCS  = $(wildcard $(SRC_DIR)/*.s) $(wildcard $(SRC_DIR)/*.c)
OBJS  = $(patsubst $(SRC_DIR)/%.s, $(OBJ_DIR)/%.o, $(filter %.s,$(SRCS))) \
        $(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(filter %.c,$(SRCS)))

# Flags
ASFLAGS  = -march=$(RV_MODE) -mabi=$(MABI_MODE)
CFLAGS   = $(ASFLAGS) -nostdlib -ffreestanding -Wall -O2
LDFLAGS  = $(ASFLAGS) -nostdlib -ffreestanding -T $(LINKER_SCRIPT)

PYTHON   = python3

# Default target
all: $(TARGET).elf dump bin $(TARGET).mem

# Build directory
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)
$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

# Assembly dosyaları için kural
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.s | $(OBJ_DIR) $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

# C dosyaları için kural
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR) $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

# Link
$(TARGET).elf: $(OBJS) $(LINKER_SCRIPT) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -o $@ $(OBJS) $(LDFLAGS)

# Generate disassembly
dump: $(TARGET).elf | $(BUILD_DIR)
	$(OBJDUMP) -M no-aliases -D $(TARGET).elf > $(TARGET).dump

# Generate raw binary
bin: $(TARGET).elf | $(BUILD_DIR)
	$(OBJCOPY) -O binary $(TARGET).elf $(TARGET).bin

# .bin'den .mem
$(TARGET).mem: $(TARGET).bin | $(BUILD_DIR)
	$(PYTHON) $(PY_BIN_PARSER) --t mem --o $@ --bin $<

# Clean build artifacts
clean:
	rm -rf $(BUILD_DIR) $(OBJ_DIR)
