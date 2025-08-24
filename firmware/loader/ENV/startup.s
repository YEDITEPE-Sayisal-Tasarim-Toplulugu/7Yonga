.section .text
.global _startup

_startup:
    la t0, trap_handler
    csrw mtvec, t0

    la sp, _estack
    
    # uart modulüne yazma
    li a0, 0x10010000
    li a1, 5208             # Clock-per-bit // 50MHz and 9600 baude rate
    sw a1, 0x00(a0)
    li a1, 0                # stop bit
    sw a1, 0x04(a0)

    # la a0, string_hello_data
    # jal ra, UART_send_string

# eğer uart programmer varsa doğrudan atlama yapılır
#ifdef IMMEDIATELY_JUMP_TO_SRAM
    li a0, 0x07000000       # sram start
    jalr ra, 0(a0)
#else
    call main
#endif

    j .              # terminate program

    nop
    nop
    nop
    nop
    nop

    .section .rodata
string_hello_data:
    .asciz          "H!\n"

