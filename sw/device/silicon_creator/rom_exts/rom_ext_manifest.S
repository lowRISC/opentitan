// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * ROM_EXT Manifest Format
 */
  .section .rom_ext_manifest, "a"

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
signed_area_start:

// Calculated by linker
image_length:
  // This should be the whole image length (of the flash part, including the
  // manifest).
  .word (rom_ext_image_end - rom_ext_image_start)

// Overriden by signing script
image_version:
  .word 0x0

// Overriden by signing script
image_timestamp:
  .dword 0x0

// Overriden by signing script
image_signature_key_public_exponent:
  .word 0x0

// reserved
  .word 0x0

// Overriden by signing script
image_usage_constraints:
  .rept 32
  .byte 0x0
  .endr

// Overriden by signing script
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

// Code Image starts here
image_code_contents:


/**
 * ROM_EXT Image End Section.
 *
 * We're having trouble with `objcopy` not honouring the FileSiz and MemSiz as
 * given in the final elf, and we want the files to be produced as rounded to
 * the next word-size up.
 *
 * The ELF Segments correctly reflect the FileSiz and MemSiz are rounded up by
 * the ALIGN(4) directives in the linker script. However, in some cases, objcopy
 * produces a binary file that is shorter than the segment FileSiz (this seems
 * to happen when the last section that contains data does not have a size
 * rounded to the next word-size). This is confusing and we don't want to have
 * to pad the binary in post-processing, so instead we added this dummy section.
 *
 * The idea behind this section is that it must be word-sized, and word-aligned.
 * It also provides a local symbol which can be used to calculate the whole
 * image length. This symbol must come after some data in the section, or the
 * padding word will not have the intended effect.
 *
 * We cannot do this in the linker script, as an output section in the linker
 * script with only symbol and data definitions (and no input section
 * inclusions) gets weird flags that we have no control over, which can lead to
 * strange segment assignments. In an assembly file, we can specify section
 * flags that will propagate in the linker script from the input section to the
 * output section.
 *
 * The particular value of the dummy `.word` does not matter, but is included in
 * the signed part of the image so will be validated by the signature.
 */
  .section .rom_ext_end, "a"
  .p2align 2
  .word 0x0

rom_ext_image_end:
