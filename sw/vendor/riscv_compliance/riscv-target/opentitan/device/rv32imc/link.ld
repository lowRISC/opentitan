/* Copyright lowRISC contributors.
   Licensed under the Apache License, Version 2.0, see LICENSE for details.
   SPDX-License-Identifier: Apache-2.0
*/

OUTPUT_ARCH("riscv")
ENTRY(_start)

/* required to correctly link newlib */
GROUP(-lc -lgloss -lgcc -lsupc++)

SEARCH_DIR(.)
__DYNAMIC  =  0;

MEMORY
{
    flash (rx) : ORIGIN = 0x20000000, LENGTH = 0x100000
    ram (wx)   : ORIGIN = 0x10000000, LENGTH = 0x10000
}

_stack_start = ORIGIN(ram) + LENGTH(ram);

/* need to move signature data to modifiable memory */
SECTIONS
{
  .text.init ORIGIN(flash) : {
    *(.text.init)
  } > flash

  .text.trap : {
    . = ALIGN(0x100);
    *(.text.trap)
  } > flash

  .text : {
    . = ALIGN(0x100);
    *(.text)
  } > flash

  .data : {
    . = ALIGN(0x100);
    *(.data.*)
  } > flash

  .tohost ORIGIN(ram) (NOLOAD) : {
    *(.tohost)
    *(.test.output)
  } > ram

  .bss : {
    . = ALIGN(0x100);
    *(.bss)
  } > ram

  _end = .;
}
