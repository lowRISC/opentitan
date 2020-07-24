/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial linker script for chip memory configuration.
 */
MEMORY {
  rom(rx) : ORIGIN = 0x00008000, LENGTH = 0x4000
  ram_main(rw) : ORIGIN = 0x10000000, LENGTH = 0x10000
  ram_ret(rw) : ORIGIN = 0x18000000, LENGTH = 0x1000
  eflash(rx) : ORIGIN = 0x20000000, LENGTH = 0x80000
}
