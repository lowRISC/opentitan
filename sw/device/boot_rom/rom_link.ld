/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan boot ROM.
 *
 * Portions of this file are Ibex-specific.
 */

OUTPUT_ARCH(riscv)
GROUP(-lgcc)

/**
 * Indicate that there are no dynamic libraries, whatsoever.
 */
__DYNAMIC = 0;

MEMORY {
  rom(rx)   : ORIGIN = 0x00008000, LENGTH = 0x2000
  ram(w)    : ORIGIN = 0x10000000, LENGTH = 0x10000
  flash(rx) : ORIGIN = 0x20000000, LENGTH = 0x100000
}

/**
 * The boot address, which indicates the location of the initial interrupt
 * vector.
 */
_boot_address = ORIGIN(rom);

_heap_size = 0xe000;
_stack_size = 0x2000;
_stack_start = ORIGIN(ram) + _heap_size + _stack_size;
_flash_start = ORIGIN(flash);

_chip_info_size = 128;
_chip_info_start = ORIGIN(rom) + LENGTH(rom) - _chip_info_size;

/**
 * NOTE: We have to align each section to word boundaries as our current
 * s19->slm conversion scripts are not able to handle non-word aligned sections.
 */
SECTIONS {
  /**
   * Ibex interrupt vector. See irq_vector.S for more information. 
   *
   * This has to be set up at the boot address, so that execution jumps to the
   * reset handler correctly.
   */
  .vectors _boot_address : ALIGN(4) {
    KEEP(*(.vectors))
    *(.vectors)
  } > rom

  /**
   * C runtime (CRT) section, containing program initialization code.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
    *(.crt)
  } > rom

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)
  } > rom

  /**
   * Read-only data section, containing all large compile-time constants, like
   * strings.
   */
  .rodata : ALIGN(4) {
    *(.rodata)
    *(.rodata.*)
  } > rom

  /**
   * "Intitial data" section, the initial values of the mutable data section 
   * initialized at runtime.
   */ 
  .idata : ALIGN(4) {
    _data_init_start = .;
  } > rom

  /** 
   * Standard mutable data section, at the bottom of RAM. This will be
   * initialized from the .idata section at runtime by the CRT.
   */ 
  .data ORIGIN(ram): AT(_data_init_start) ALIGN(4) {
    _data_start = .;
    *(.data)
    *(.data.*)
    *(.sdata)
    _data_end = .;
  } > ram

  /**
   * Immutable chip_info data, containing build-time-recorded information.
   */
  .chip_info _chip_info_start : ALIGN(4) {
    *(.chip_info)
  } > rom

  /**
   * Standard BSS section. This will be zeroed at runtime by the CRT.
   */
  .bss : ALIGN(4) {
    _bss_start = .;
    *(.bss)
    *(.bss.*)
    *(.sbss)
    *(.sbss.*)
    *(COMMON)
    _bss_end = .;
  } > ram

  /**
   * STAB debug table.
   */
  .stab 0x0 (NOLOAD): {
    [.stab]
  }

  /**
   * STAB debug strings.
   */
  .stabstr 0x0 (NOLOAD): {
    [.stabstr]
  }
}
