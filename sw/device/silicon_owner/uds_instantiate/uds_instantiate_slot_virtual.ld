/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Virtual-slot linker script for `uds_instantiate` (first Silicon Owner stage).
 *
 * Preserves `.static_critical` and `.static_dice` (NOLOAD) at the base of
 * `ram_main` so `static_dice_mldsa_cdi.uds_pub` handed over by ML-DSA ROM_EXT
 * is not overwritten by CRT initialization.
 */

INCLUDE hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld

_slot_start_address = ORIGIN(owner_virtual) + _rom_ext_size;
_slot_size = LENGTH(owner_virtual) - _rom_ext_size;

REGION_ALIAS("owner_flash", owner_virtual);
REGION_ALIAS("coverage_flash", owner_flash);

OUTPUT_ARCH(riscv)

__DYNAMIC = 0;

ENTRY(_start_boot)

/* DV Log offset (must differ from ROM and ROM_EXT). */
_dv_log_offset = 0x20000;

_manifest_code_start = _text_start - _slot_start_address;
_manifest_code_end = _text_end - _slot_start_address;
_manifest_entry_point = _start_boot - _slot_start_address;
_manifest_address_translation = (_text_start >= ORIGIN(eflash) &&
                                 _text_start < (ORIGIN(eflash)
                                              + LENGTH(eflash))) ? 0x1d4 : 0x739;

SECTIONS {
  .manifest _slot_start_address : {
    _manifest_base_address = .;
    KEEP(*(.manifest))
    . = ALIGN(256);
  } > owner_flash

  .vectors : ALIGN(256) {
    _text_start = .;
    KEEP(*(.vectors))
  } > owner_flash

  .crt : ALIGN(4) {
    KEEP(*(.crt))
  } > owner_flash

  .text : ALIGN(4) {
    *(.text)
    *(.text.*)
    . = ALIGN(4);
    _text_end = .;
  } > owner_flash

  .rodata : ALIGN(4) {
    *(.srodata)
    *(.srodata.*)
    *(.rodata)
    *(.rodata.*)
    . = ALIGN(4);
  } > owner_flash

  INCLUDE sw/device/lib/coverage/rodata.ld

  /**
   * Critical static data shared with ROM / ROM_EXT, followed by DICE SRAM
   * handoff structures (`static_dice_cdi_0` and `static_dice_mldsa_cdi`).
   */
  INCLUDE sw/device/silicon_creator/lib/base/static_critical.ld
  INCLUDE sw/device/silicon_creator/lib/base/static_dice.ld

  .data : ALIGN(4) {
    _data_start = .;
    _data_init_start = LOADADDR(.data);
    __global_pointer$ = . + 2048;

    *(.sdata)
    *(.sdata.*)
    *(.data)
    *(.data.*)

    . = ALIGN(4);
    _data_end = .;
    _data_init_end = LOADADDR(.data) + SIZEOF(.data);
  } > ram_main AT> owner_flash

  .bss : ALIGN(4) {
    _bss_start = .;
    *(.sbss)
    *(.sbss.*)
    *(.bss)
    *(.bss.*)
    . = ALIGN(4);
    _bss_end = .;
  } > ram_main

  INCLUDE sw/device/lib/coverage/bss.ld

  INCLUDE sw/device/info_sections.ld
}

ASSERT(
  SIZEOF(.static_dice) == 1220 + 18988,
  "Error: .static_dice sections must match ML-DSA ROM_EXT layout.");
