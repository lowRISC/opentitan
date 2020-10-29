/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*

  OTBN has a pure Harvard architecture, with instruction and data
  memory both starting at address 0.

  This linker script template is interpolated by otbn-ld after it gets
  the LMAs and memory sizes from otbn.hjson.

*/
MEMORY
{
    imem (x)  : ORIGIN = 0, LENGTH = ${imem_length}
    dmem (rw) : ORIGIN = 0, LENGTH = ${dmem_length}

    /* LMA addresses (for VMAs in imem/dmem, respectively) */
    imem_load (rw) : ORIGIN = ${imem_lma}, LENGTH = ${imem_length}
    dmem_load (rw) : ORIGIN = ${dmem_lma}, LENGTH = ${dmem_length}
}

SECTIONS
{
    .text ORIGIN(imem) : ALIGN(4)
    {
        _imem_start = .;

        *(.text*)

        /* Align section end. Shouldn't really matter, but might make binary
           blobs a bit easier to work with. */
        . = ALIGN(4);

        _imem_end = .;
    } >imem AT>imem_load

    .data ORIGIN(dmem) : ALIGN(32)
    {
        _dmem_start = .;

        *(.data*)
        . = ALIGN(32);
        *(.bss*)

        /* Align section end (see note in .text section) */
        . = ALIGN(4);

        _dmem_end = .;
    } >dmem AT>dmem_load
}
