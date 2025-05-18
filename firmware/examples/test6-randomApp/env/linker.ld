ENTRY(_start)

MEMORY
{
  /* Define the memory regions */
  ram (rwx) : ORIGIN = 0x80000000, LENGTH = 120K
}

SECTIONS
{
  /* Define the sections of the output file */
  .text : {
    *(.text)
  } > ram

  .data : {
    *(.data)
  } > ram

  .bss : {
    . = ALIGN(4);
    _bss_start = . ;

    *(.bss)
  } > ram

  .sdata : {
    *(.sdata)
  } > ram

  .sbss : {
    . = ALIGN(4);
    _sbss_start = . ;
    *(.sbss)
  } > ram

  . = ALIGN(4);
  _end = . ;
}