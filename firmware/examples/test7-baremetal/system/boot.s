.globl boot_main
boot_main:
    li sp, 0x80019000 # 100kb
    
    jal ra, core_init
    jal ra, main

    lui x0, 10
    j .
