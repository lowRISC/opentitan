/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Variables stored in the .static_critical section of RAM.
 *
 * This should be included into a NOLOAD .static_critical section located at
 * the origin of main RAM.
 */
ASSERT(. == ORIGIN(ram_main), "Error: .static_critical section not at the base address of main RAM.");
ASSERT(. - ADDR(.static_critical) == 0, "Error: .static_critical.sec_mmio_ctx section offset has changed.");
KEEP(*(.static_critical.sec_mmio_ctx))
ASSERT(. - ADDR(.static_critical) == 816, "Error: .static_critical.sec_mmio_ctx section size has changed");
