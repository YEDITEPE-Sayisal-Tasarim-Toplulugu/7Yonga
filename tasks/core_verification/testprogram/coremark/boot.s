.globl _start
_start:
    # load sbss start and end address in t0 and t1 to clear bss
    
     lui t0,%hi(_sbss_start)
     add t0,t0,%lo(_sbss_start)
     
     # t1 = _end
     lui t1,%hi(_end)
     add t1,t1,%lo(_end)
 bss_clear:
     sw x0,  (0)(t0)        # Write 0x00 to mem[t0]
     add t0, t0, 4          # t0 += 4
     blt t0, t1, bss_clear  # Branch back to bss_clear if (t0 < t1)

    li x2, 0x00002000 # stack pointer (24K)
	
    jal ra, notmain
    
    # test passed signal
    li a0, 0x20000000
    li a1, 123456789
    sw a1, 0(a0)

    j .
