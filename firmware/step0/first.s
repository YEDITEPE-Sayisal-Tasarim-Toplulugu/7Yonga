.section .text
.global _start

_start:
    li a0, 42        # Load 42 into a0
    li a7, 93        # syscall number for exit
    
    # test passed signal
    li a0, 0x20000000
    li a1, 123456789
    sw a1, 0(a0)

    # buyruk belleğine yazma
    li a0, 0x00000800
    li a1, 123456789
    sw a1, 0(a0)

    # uart modulüne yazma
    li a0, 0x10010000
    # li a1, 10416          # Clock-per-bit // 100MHz and 9600 baude rate
    li a1, 5208             # Clock-per-bit // 50MHz and 9600 baude rate
    sw a1, 0x00(a0)
    li a1, 0                # stop bit
    sw a1, 0x04(a0)
    li a1, 65               # Transmit data
    sw a1, 0x0C(a0)
    li a1, 3                # Transmit enable bit
    sw a1, 0x10(a0)

    li a2, 1
    la a3, string_data
send_char:
    lb a1, 0(a3)
    sb a1, 0x0C(a0)
    sw a2, 0x10(a0)
.L1:
    lw t1, 0x10(a0)
    andi t1, t1, 7
    srli t1, t1, 2
    beq t1, zero, .L1
    addi a3, a3, 1
    bne a1, zero, send_char

    j .              # terminate program

    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    .section .rodata
string_data:
    .asciz          "Hello World!"
