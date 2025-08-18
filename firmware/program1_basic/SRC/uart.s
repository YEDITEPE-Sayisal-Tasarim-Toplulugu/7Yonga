    .section .text
    .global UART_send_string

    .equ UART_BASE, 0x10010000

# void UART_send_string(const char *str);
# a0 = str pointer
UART_send_string:
    # --- Prologue ---
    addi sp, sp, -12
    sw ra, 8(sp)
    sw s0, 4(sp)

    mv s0, a0              # s0 = string pointer
    li s1, UART_BASE       # sabit UART base

    li t0, 1               # transmit başlat

.Lloop:
    lb t1, 0(s0)
    beq t1, zero, .Lend    # null terminator -> çık
    sb t1, 0x0C(s1)        # TX data
    sw t0, 0x10(s1)        # gönderimi başlat

.Lwait:
    lw t2, 0x10(s1)        # status oku
    andi t2, t2, 7
    srli t2, t2, 2
    beq t2, zero, .Lwait

    addi s0, s0, 1
    j .Lloop

.Lend:
    # --- Epilogue ---
    lw ra, 8(sp)
    lw s0, 4(sp)
    addi sp, sp, 12
    ret
    