# Makefile for assembling a RISC-V assembly file into an ELF binary using custom linker script

# RISC-V toolchain prefix
CROSS_COMPILE = riscv64-unknown-elf-

AS      = $(CROSS_COMPILE)as
CC      = $(CROSS_COMPILE)gcc
LD      = $(CROSS_COMPILE)ld
OBJDUMP = $(CROSS_COMPILE)objdump
OBJCOPY = $(CROSS_COMPILE)objcopy
PY_BIN_PARSER	?= ../riscv_tool_hexdump.py

# Architecture settings
RV_MODE   = rv32i
MABI_MODE = ilp32

# Files
TARGET = program
SRC    = first.s
LINKER_SCRIPT = linker.ld

# Flags
ASFLAGS  = -march=$(RV_MODE) -mabi=$(MABI_MODE)
CFLAGS   = $(ASFLAGS) -nostdlib
LDFLAGS  = $(ASFLAGS) -nostdlib -T $(LINKER_SCRIPT)

PYTHON	 = python3

# Targets
all: $(TARGET).elf dump bin $(TARGET).mem

# Compile and link
$(TARGET).elf: $(SRC) $(LINKER_SCRIPT)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

# Generate disassembly
dump: $(TARGET).elf
	$(OBJDUMP) -M no-aliases -D $(TARGET).elf > $(TARGET).dump

# Generate raw binary
bin: $(TARGET).elf
	$(OBJCOPY) -O binary $(TARGET).elf $(TARGET).bin

# .bin'den .mem
$(TARGET).mem: $(TARGET).bin
	$(PYTHON) $(PY_BIN_PARSER) --t mem --o $@ --bin $<

# Clean build artifacts
clean:
	rm -f $(TARGET).elf $(TARGET).dump $(TARGET).bin
