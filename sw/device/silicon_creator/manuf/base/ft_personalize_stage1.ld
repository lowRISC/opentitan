/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH(riscv)
ENTRY(sram_start)

MEMORY {
  ram_main (rwx) : ORIGIN = 0x10000000, LENGTH = 0x20000 /* 128 KiB */
}

_ottf_start_address = ORIGIN(ram_main);

_manifest_code_start = _text_start - ORIGIN(ram_main);
_manifest_code_end = _text_end - ORIGIN(ram_main);
_manifest_entry_point = sram_start - ORIGIN(ram_main);
_manifest_address_translation = 0x739; /* kHardenedBoolTrue for SRAM */

_dv_log_offset = 0x10000;

SECTIONS {
  . = ORIGIN(ram_main);

  .manifest : {
    _manifest_base_address = .;
    KEEP(*(.manifest))
    . = ALIGN(4);
  } > ram_main

  .text : {
    _text_start = .;
    KEEP(*(.sram_start))
    *(.crt)
    *(.text)
    *(.text.*)
    . = ALIGN(4);
    _text_end = .;
  } > ram_main

  .rodata : {
    *(.rodata)
    *(.rodata.*)
    . = ALIGN(4);
  } > ram_main

  .data : {
    *(.data)
    *(.data.*)
    . = ALIGN(4);
  } > ram_main

  .bss : {
    _bss_start = .;
    *(.bss)
    *(.bss.*)
    *(COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  _stack_end = ORIGIN(ram_main) + LENGTH(ram_main);

  INCLUDE sw/device/info_sections.ld

  /DISCARD/ : {
    *(.riscv.attributes)
    *(.comment)
    *(.ot.status_create_record)
  }
}
