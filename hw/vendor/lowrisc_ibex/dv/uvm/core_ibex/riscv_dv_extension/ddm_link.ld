/* Copyright lowRISC contributors.
   Licensed under the Apache License, Version 2.0, see LICENSE for details.
   SPDX-License-Identifier: Apache-2.0 */

/*
 * This linker script maps the generated debug test code into a discrete region
 * of the address space, representative of an external discrete debug module (ddm).
 * i.e. when +discrete_debug_module=1
 *
 * It also provisions space for a debug module "scratch" area that follows the debug
 * ROM. This allows us to test stores into the debug module without modifying
 * the test program.
 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY
{
  main : ORIGIN = 0x80000000, LENGTH = 0x100000
  dm   : ORIGIN = 0x1A110000, LENGTH = 0x1000
}

_dm_scratch_len = 0x100;

SECTIONS
{
  .text : {
    *(.text)
    . = ALIGN(0x1000);
  } >main
  .tohost : {
    . = ALIGN(4);
    *(.tohost)
    . = ALIGN(0x1000);
  } >main
  .page_table : {
    *(.page_table)
  } >main
  .data : {
    *(.data)
  } >main
  .user_stack : {
    *(.user_stack)
  } >main
  .kernel_data : {
    *(.kernel_data)
  } >main
  .kernel_stack : {
    *(.kernel_stack)
  } >main
  .bss : {
    *(.bss)
  } >main

  _end = .;

  .debug_module : {
    *(.debug_module)
  } >dm
  .dm_scratch : {
    . = ALIGN(4);
    . = . + _dm_scratch_len ;
    . = ALIGN(4);
    } >dm =0
}
