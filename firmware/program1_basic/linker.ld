/* M. Furkan UZUN */

/* The OUTPUT_ARCH command specifies the machine architecture where the
   argument is one of the names used in the BFD library. More
   specifically one of the entires in bfd/cpu-mips.c */
OUTPUT_ARCH( "riscv" )

/* Entry Point */
ENTRY( _startup )

GROUP( -lc -lgloss -lgcc )

/* Highest address of the user mode stack */
_estack = ORIGIN(DMEM) + LENGTH(DMEM); /* end of "DMEM" Ram type memory */

MEMORY
{
    /* Bellek bölgeleri */
    IMEM (rx)  : ORIGIN = 0x00000800, LENGTH = 8K    /* Kod ve sabit veri */
    DMEM (rwx) : ORIGIN = 0x20000000, LENGTH = 8K    /* Çalışma zamanı veri, stack, heap */
}

SECTIONS
{
    /* Kod (.text) ROM’a */
    .text : {
        . = ALIGN(4);
        *(.text)            /* .text sections (code) */
        *(.text.*)          /* .text* sections (code) */
        . = ALIGN(4);
        _etext = .;         /* define a global symbols at end of code */
    } > IMEM

    /* rodata: Read-only data */
    .rodata : {
        . = ALIGN(4);
        *(.rodata)          /* .rodata sections (constants, strings, etc.) */
        *(.rodata.*)        /* .rodata* sections (constants, strings, etc.) */
        . = ALIGN(4);
    } > IMEM

    /* Used by the startup to initialize data */
    _sidata = LOADADDR(.data);

    .data : {
        _sdata = .;
         *(.data)
        *(.data.*)
        *(.gnu.linkonce.d.*)
        . = ALIGN(4);
        _edata = .;
    } > DMEM AT > IMEM

    . = ALIGN(16);
    _gp = . + 0x800;

    _ssidata = LOADADDR(.sdata);

     /* Writable small data segment */
    .sdata : {
        _ssdata = .;
        *(.sdata)
        *(.sdata.*)
        *(.srodata.*)
        *(.gnu.linkonce.s.*)
        . = ALIGN(4);
        _esdata = .;
    } > DMEM AT > IMEM

    /* Sıfırlanacak .bss RAM’de */
    . = ALIGN(4);
    .bss (NOLOAD) : {
        /* This is used by the startup in order to initialize the .bss section */
        _sbss = .;         /* define a global symbol at bss start */
        __bss_start__ = _sbss;
        *(.bss)
        *(.bss.*)
        *(COMMON)
        
        . = ALIGN(4);
        _ebss = .;         /* define a global symbol at bss end */
        __bss_end__ = _ebss;
    } > DMEM

    /* Program sonu adresi (heap başlangıcı için kullanılabilir) */
    . = ALIGN(4);
    _end = .;
}
