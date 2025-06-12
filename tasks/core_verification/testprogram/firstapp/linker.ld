ENTRY(_start)

MEMORY
{
  /* Define the memory regions */
  ram (rwx) : ORIGIN = 0x30000000, LENGTH = 1K
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

  . = ALIGN(4);
  _end = . ;
}