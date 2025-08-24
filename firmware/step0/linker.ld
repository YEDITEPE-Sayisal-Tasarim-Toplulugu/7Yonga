/* Entry Point */
ENTRY(_start)

/* Highest address of the user mode stack */
_estack = ORIGIN(RAM) + LENGTH(RAM); /* end of "RAM" Ram type memory */

MEMORY
{
    /* Bellek bölgeleri */
    rom (rx)  : ORIGIN = 0x00000000, LENGTH = 2K    /* Kod ve sabit veri */
    ram (rwx) : ORIGIN = 0x20000000, LENGTH = 8K    /* Çalışma zamanı veri, stack, heap */
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
    } > rom

    /* Sabit veri (.rodata) ROM’a */
    .rodata : {
        . = ALIGN(4);
        *(.rodata)          /* .rodata sections (constants, strings, etc.) */
        *(.rodata.*)        /* .rodata* sections (constants, strings, etc.) */
        . = ALIGN(4);
    } > rom

    /* Used by the startup to initialize data */
    _sidata = LOADADDR(.data);

    /* Başlangıçta RAM’e kopyalanacak .data */
    .data : {
        . = ALIGN(4);
        _sdata = .;         /* create a global symbol at data start */
        *(.data)            /* .data sections */
        *(.data.*)          /* .data* sections */
        . = ALIGN(4);
        _edata = .;         /* define a global symbol at data end */
    } > ram AT > rom

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
    } > ram

    /* Program sonu adresi (heap başlangıcı için kullanılabilir) */
    . = ALIGN(4);
    _end = .;
}
