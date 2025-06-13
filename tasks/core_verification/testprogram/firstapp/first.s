.section .text
.global _start

_start:
    li a0, 42        # Load 42 into a0
    li a7, 93        # syscall number for exit
    
    # test passed signal
    li a0, 0x20000000
    li a1, 123456789
    # sw a1, 0(a0)

    j tohost_exit

    j .              # terminate program

.globl tohost_exit
tohost_exit:
        slli a0, a0, 1
        ori a0, a0, 1

        la t0, tohost
        sw a0, 0(t0)

        1: j 1b

# to communicate with the host
# check riscv-software-src/riscv-tests
.section .tohost, "aw", @progbits

.align 6
.globl tohost
tohost: .dword 0

.align 6
.globl fromhost
fromhost: .dword 0
