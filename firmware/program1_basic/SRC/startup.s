    .section .text
    .global _startup
    .option norvc        # (opsiyonel) RVC kapatma

_startup:
    # 1. Stack pointer’ı ayarla
    la sp, _estack

    # (opsiyonel) Sistem init fonksiyonunu çağır
    # call SystemInit

    # 2. .data segmentini flash’tan RAM’e kopyala
    # .data taşıma
    la a0, _sdata
    la a1, _edata
    la a2, _sidata
    jal CopyData

    # .sdata taşıma
    la a0, _ssdata
    la a1, _esdata
    la a2, _ssidata
    jal CopyData

    jal x0, ClearBss

CopyData:
CopyDataLoop:
    beq a0, a1, CopyDataDone
    lw t0, 0(a2)         # flash’tan kelime yükle
    sw t0, 0(a0)         # RAM’e yaz
    addi a0, a0, 4
    addi a2, a2, 4
    j CopyDataLoop

CopyDataDone:
    ret

ClearBss:
    # 3. .bss segmentini sıfırla
    la a0, _sbss
    la a1, _ebss

ClearBssLoop:
    beq a0, a1, ClearBssDone
    sw zero, 0(a0)
    addi a0, a0, 4
    j ClearBssLoop

ClearBssDone:

    # 4. main fonksiyonuna geç
    call main

    # Eğer main dönerse sonsuz döngüye gir
HangForever:
    j HangForever

    nop
    nop
    nop
    nop
    nop
