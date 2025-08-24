    .section .text
    .global trap_handler

trap_handler:
    # Prologue
    addi sp, sp, -16
    sw ra, 12(sp)
    sw s0, 8(sp)
    sw s1, 4(sp)

    # mcause al
    csrr a0, mcause
    la   a1, str_mcause
    jal  ra, UART_send_reg_hex

    # mtval al
    csrr a0, mtval
    la   a1, str_mtval
    jal  ra, UART_send_reg_hex

    # mepc al
    csrr a0, mepc
    la   a1, str_mepc
    jal  ra, UART_send_reg_hex

    # sonsuz loop
1:  j 1b

    # Epilogue (hiç dönmeyecek)
    lw ra, 12(sp)
    lw s0, 8(sp)
    lw s1, 4(sp)
    addi sp, sp, 16
    mret

    .section .rodata
str_mcause: .asciz "MCAUSE="
str_mtval:  .asciz "MTVAL="
str_mepc:   .asciz "MEPC="
