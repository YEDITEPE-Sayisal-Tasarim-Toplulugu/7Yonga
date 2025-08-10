ENTRY(_start)

MEMORY
{
  /* Define memory regions according to addr_rule_t */
  rom (rx)  : ORIGIN = 0x00000000, LENGTH = 1K    /* 0x1000_0000 - 0x1000_0400 */
  ram (rwx) : ORIGIN = 0x20000000, LENGTH = 8K    /* 0x3000_0000 - 0x3000_2000 */
}

SECTIONS
{
  /* Instruction memory section (.text) goes into ROM */
  .text : {
    *(.text)
  } > rom

  /* Data memory section (.data) goes into RAM */
  .data : {
    *(.data)
  } > ram

  /* Stack and heap (optional, if needed) */

  . = ALIGN(4);
  _end = . ;
}
