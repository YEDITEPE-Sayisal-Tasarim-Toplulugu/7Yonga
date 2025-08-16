.section .text
.global _start

_start:
    la sp, _estack
    
    # uart modulüne yazma
    li a0, 0x10010000
    li a1, 5208             # Clock-per-bit // 50MHz and 9600 baude rate
    sw a1, 0x00(a0)
    li a1, 0                # stop bit
    sw a1, 0x04(a0)

    la a0, string_hello_data
    jal ra, UART_send_string

    j .              # terminate program

    nop
    nop
    nop
    nop
    nop

    .section .rodata
string_hello_data:
    .asciz          "Hello World!\n"

