// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * ROM_EXT Manifest Format
 */
  .section .rom_ext_manifest, "a"

  .globl rom_ext_image_start
rom_ext_image_start:

// Constant
rom_ext_identifier:
  .word 0x4552544F

// Reserved
  .word 0x0

// Will be overidden by signing script
image_signature:
  .rept 96
  .word 0x0
  .endr

// Everything beyond this point is signed.

  .extern rom_ext_full_image_size
// Calculated by linker
image_length:
  // This should be the whole image length (of the flash part, including the
  // manifest).
  .word rom_ext_full_image_size

// Overriden by signing script
image_version:
  .word 0x0

// Overriden by signing script
image_timestamp:
  .dword 0x0

// Overridden by signing script
image_signature_algorithm:
  .word 0x0

// Overriden by signing script
image_signature_exponent:
  .word 0x0

// Maybe: Overriden by signing script?
image_usage_constraints:
  .word 0x0

// Reserved
  .word 0x0

// Overriden by signing script
image_software_binding_tag:
  .rept 16
  .byte 0x0
  .endr

// Maybe: Overriden by signing script?
image_peripheral_lockdown_info:
  .rept 16
  .byte 0x0
  .endr

// Overriden by signing script
signature_public_key:
  .rept 96
  .word 0x0
  .endr

// Extensions
extensions:
  .rept 4
  .word 0x0
  .word 0x0
  .endr

  .globl image_code_contents
// Code Image starts here
image_code_contents:
