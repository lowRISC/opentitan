/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * NOTE:
 * Common portion of a CHERIoT linker script for an NVM boot stage. Not usable
 * on its own; a slot script defines `_slot_start_address` and the `cheriot_nvm`
 * region alias, then includes this.
 *
 * Covers text and rodata. A program with mutable data also needs `.data` and
 * `.bss`, plus a CRT that materialises capabilities from `__cap_relocs`, since
 * the linker leaves the capability slots in `.data` as fill.
 */

OUTPUT_ARCH(riscv)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

/**
 * Marking the entry point correctly for the ELF file. The signer tool will
 * transfer this value to the `entry_point` field of the manifest, which
 * whichever stage boots this image then uses to hand over execution.
 */
ENTRY(_start_boot)

/*
 * Manifest fields that depend on the link, consumed by the image's `.manifest`
 * section. These mirror the definitions in `bare_metal_common.ld`.
 */
_manifest_code_start = _text_start - _slot_start_address;
_manifest_code_end = _text_end - _slot_start_address;
_manifest_entry_point = _start_boot - _slot_start_address;

/*
 * The value kHardenedBoolFalse (0x1d4) is selected if the code is linked in
 * the NVM region.  Otherwise, the value kHardenedBoolTrue (0x739) is
 * selected.
 */
_manifest_address_translation = (_text_start >= ORIGIN(nvm) &&
                                 _text_start < (ORIGIN(nvm)
                                              + LENGTH(nvm))) ? 0x1d4 : 0x739;

SECTIONS {
  .manifest _slot_start_address : {
    KEEP(*(.manifest))
    . = ALIGN(256);
  } > cheriot_nvm

  /**
   * Ibex interrupt vector, which must be 256-byte aligned.
   */
  .vectors : ALIGN(256) {
    _text_start = .;
    KEEP(*(.vectors))
  } > cheriot_nvm

  .crt : ALIGN(4) {
    KEEP(*(.crt))
  } > cheriot_nvm

  .text : ALIGN(4) {
    *(.text)
    *(.text.*)

    /* Ensure section end is word-aligned. */
    . = ALIGN(4);
    _text_end = .;
  } > cheriot_nvm

  /**
   * A CHERIoT capability occupies 8 bytes of addressable memory (plus a
   * validity tag held out of band), so anything that can hold one is 8-byte
   * aligned.
   */
  .rodata : ALIGN(8) {
    *(.srodata)
    *(.srodata.*)
    *(.rodata)
    *(.rodata.*)
  } > cheriot_nvm

  /**
   * Bounds and permissions for each static capability, to be materialised by a
   * CRT.
   */
  __cap_relocs : ALIGN(8) {
    __cap_relocs_start = .;
    KEEP(*(__cap_relocs))
    __cap_relocs_end = .;
  } > cheriot_nvm

  INCLUDE sw/device/info_sections.ld
}
