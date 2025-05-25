.section .text
.global _start

_start:
    li a0, 42        # Load 42 into a0
    li a7, 93        # syscall number for exit
    j .              # terminate program
