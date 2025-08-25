# 7Yonga

TARGET_LIB_NAME		?= Yonga7std
CROSS_COMPILE 		?= riscv64-unknown-elf-

# Toolchain ayarları
AS        			= $(CROSS_COMPILE)as
CC        			= $(CROSS_COMPILE)gcc
LD        			= $(CROSS_COMPILE)ld
OBJDUMP   			= $(CROSS_COMPILE)objdump
OBJCOPY   			= $(CROSS_COMPILE)objcopy
AR        			= $(CROSS_COMPILE)ar

INC_DIR				= inc
SRC_DIR				= src
OBJ_DIR 			= obj

# Mimari ayarları
RV_MODE   			= rv32imzicsr
MABI_MODE 			= ilp32

CFLAGS    			= -march=$(RV_MODE) -mabi=$(MABI_MODE) -Wall -O2 -nostdlib -nostartfiles -ffreestanding -I$(INC_DIR)
ASFLAGS   			= -march=$(RV_MODE) -mabi=$(MABI_MODE)

# Diziler	
SRC_C     			= $(wildcard $(SRC_DIR)/*.c)
SRC_S     			= $(wildcard $(SRC_DIR)/*.S)
OBJ_C     			= $(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(SRC_C))
OBJ_S     			= $(patsubst $(SRC_DIR)/%.S, $(OBJ_DIR)/%.o, $(SRC_S))
OBJS      			= $(OBJ_C) $(OBJ_S)

TARGET    			= lib$(TARGET_LIB_NAME).a

# Varsayılan hedef
all: $(TARGET)

# Kütüphane oluşturma
$(TARGET): $(OBJS)
	$(AR) rcs $@ $(OBJS)

# C kaynaklarını derle
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

# Assembly kaynaklarını derle
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.S | $(OBJ_DIR)
	$(CC) $(ASFLAGS) -c $< -o $@

# obj klasörünü oluştur
$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

dump: $(TARGET)
	$(LD) -o temp.elf -Ttext=0x0 $(TARGET)
	$(OBJDUMP) -M no-aliases -D temp.elf > lib$(TARGET_LIB_NAME).dump
	rm -rf temp.elf

# Temizlik
clean:
	rm -rf $(OBJ_DIR) $(TARGET) lib$(TARGET_LIB_NAME).dump

.PHONY: all clean
