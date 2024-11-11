/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * TODO(#24368): Adapt the linker script for real IMM_ROM_EXT. This linker
 * script only works for hello-world IMM_ROM_EXT.
 */
OUTPUT_ARCH(riscv)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/* DV Log offset (has to be different to other boot stages). */
_dv_log_offset = 0x10000;

ENTRY(_imm_rom_ext_start_boot)

SECTIONS {
  .rom_ext_immutable : ALIGN(4) {
    /* Ibex */
    *(.vectors)
    . = ALIGN(256);
    /* CRT */
    *(.crt)
    . = ALIGN(4);
    /* Text */
    *(.text)
    *(.text.*)
    . = ALIGN(4);
    /* Read-only Data */
    *(.srodata)
    *(.srodata.*)
    *(.rodata)
    *(.rodata.*)
    . = ALIGN(4);
    *(.data)
    . = ALIGN(4);
    *(.bss)
    . = ALIGN(4);
  }

  INCLUDE sw/device/info_sections.ld
}
