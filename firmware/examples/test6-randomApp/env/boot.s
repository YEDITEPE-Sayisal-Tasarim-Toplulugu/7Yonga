.globl _start

_start:
    li x20, 0x20000000 	# UART CTRL REG

	addi x1, x0, 3
	addi x2, x0, ((50*1000000)/115200)-1
	slli x2, x2, 16
	or x1, x1, x2
	sw x1, 0(x20)

    addi x1, x0, 0
    addi x20, x0, 0

    # li x2, 0x80005FE8 # stack pointer (24K)
    # li x2, 0x8000C350 # stack pointer (50K)
    li x2, 0x8001E000 # stack pointer (50K)

    jal ra, main
    ecall
    j .
