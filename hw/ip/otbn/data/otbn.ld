/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*

  OTBN has a pure Harvard architecture, with instruction and data
  memory both starting at address 0.

  We give each 1MiB of space: too much for the eventual chip - let's
  come back to this once we know how much space we'll have or (harder)
  auto-generate it from the address map.

*/
MEMORY
{
    imem (x)  : ORIGIN = 0, LENGTH = 1M
    dmem (rw) : ORIGIN = 0, LENGTH = 1M

    /* LMA addresses (for VMAs in imem/dmem, respectively) */
    imem_load (rw) : ORIGIN = 1M, LENGTH = 1M
    dmem_load (rw) : ORIGIN = 1M, LENGTH = 1M
}

SECTIONS
{
    .text ALIGN(4) :
    {
        *(.text*)
    } >imem AT >imem_load

    .data ALIGN(32) :
    {
        *(.data*)
        . = ALIGN(32);
        *(.bss*)
    } >dmem AT >dmem_load
}
