.section .text
.global _start

_start:
    li a0, 42        # Load 42 into a0
    li a7, 93        # syscall number for exit
    
    # test passed signal
    li a0, 0x20000000
    li a1, 123456789
    sw a1, 0(a0)

    j .              # terminate program
