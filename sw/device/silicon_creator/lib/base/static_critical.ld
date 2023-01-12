/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Variables stored in the .static_critical section of RAM.
 *
 * This file should be included inside of a `SECTIONS` block where a
 * `ram_main` memory is defined, and should come before all other main
 * memory sections.
 */

.static_critical ORIGIN(ram_main) (NOLOAD) : ALIGN(4) {
  dummy = .;
  ram_origin = ORIGIN(ram_main);
/*  ASSERT(
    . == 0xe0000000,
    "Error: .static_critical section not at the base address of main RAM.");
*/
  KEEP(*(.static_critical.boot_measurements))
  KEEP(*(.static_critical.epmp_state))
  KEEP(*(.static_critical.sec_mmio_ctx))
  static_critical1 = SIZEOF(.static_critical);
  static_critical2 = _static_critical_size;
  
/*
  ASSERT(
    SIZEOF(.static_critical) == _static_critical_size,
    "Error: .static_critical section size has changed");*/
} > ram_main
