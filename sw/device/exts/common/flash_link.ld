/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Linker script for an OpenTitan flash binaries.
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
  ram(w)    : ORIGIN = 0x10000000, LENGTH = 0x10000
  flash(rx) : ORIGIN = 0x20000000, LENGTH = 0x100000
}

/**
 * The stack starts at the end of RAM and grows down.
 */
_stack_start = ORIGIN(ram) + LENGTH(ram);

SECTIONS {
  /**
   * The flash header. This will eventually contain other stuff, like a 
   * signature, but for now it's just the entry point at offset zero.
   */
  .flash_header ORIGIN(flash): ALIGN(4) {
    /** 
     * NOTE:ld scripts do not provide a mechanism to refer to ENTRY, 
     * so we just harcode the _start symbol.
     */
    LONG(_start)
  } > flash

  /**
   * C runtime (CRT) section, containing program initialization code.
   *
   * We don't use ENTRY, so the start of |flash| acts as the entrypoint. Since
   * the CRT is the first thing that needs to run, it goes at the top.
   */
  .crt : ALIGN(4) {
    KEEP(*(.crt))
    *(.crt)
  } > flash

  /**
   * Ibex interrupt vector. See sw/device/lib/irq_vectors.S for more information.
   *
   * The 256-byte alignment is required by Ibex's vectoring mechanism.
   */
  .vectors : ALIGN(0x100) {
    _vectors_start = .;
    KEEP(*(.vectors))
    *(.vectors)
  } > flash

  /**
   * Standard text section, containing program code.
   */
  .text : ALIGN(4) {
    *(.text)
    *(.text.*)
  } > flash

  /**
   * Read-only data section, containing all large compile-time constants, like
   * strings.
   */
  .rodata : ALIGN(4) {
    *(.rodata)
    *(.rodata.*)
  } > flash

  /**
   * "Intitial data" section, the initial values of the mutable data section 
   * initialized at runtime.
   */ 
  .idata : ALIGN(4) {
    _data_init_start = .;
  } > flash

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
    *(.stab)
  }

  /**
   * STAB debug strings.
   */
  .stabstr 0x0 (NOLOAD): {
    *(.stabstr)
  }
}
