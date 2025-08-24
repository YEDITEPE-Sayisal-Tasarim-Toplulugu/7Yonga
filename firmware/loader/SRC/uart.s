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

    .global UART_send_reg_hex
# void UART_send_reg_hex(uint32_t value, const char *prefix)
UART_send_reg_hex:
    addi sp, sp, -32
    sw ra, 28(sp)
    sw s0, 24(sp)
    sw s1, 20(sp)

    mv s0, a0       # value
    mv s1, a1       # prefix

    # prefix yazdır
    mv a0, s1
    jal ra, UART_send_string

    # hex için buffer hazırla
    la t0, hex_buffer
    li t1, 8         # 8 digit (32-bit)

1:  srli t2, s0, 28  # en üst nibble (32-bit için 28, 24, 20... sırasıyla kaydıracağız)
    li t3, 10
    blt t2, t3, 2f
    addi t2, t2, 55  # 'A'-10
    j 3f
2:  addi t2, t2, 48  # '0'
3:  sb t2, 0(t0)
    addi t0, t0, 1
    slli s0, s0, 4   # sonraki nibble
    addi t1, t1, -1
    bnez t1, 1b

    # null terminate
    sb zero, 0(t0)

    la a0, hex_buffer
    jal ra, UART_send_string

    la a0, newline
    jal ra, UART_send_string

    lw ra, 28(sp)
    lw s0, 24(sp)
    lw s1, 20(sp)
    addi sp, sp, 32
    ret

    .section .bss
    .align 4
hex_buffer: .space 12

    .section .rodata
newline: .asciz "\n"
