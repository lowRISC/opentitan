/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial linker script for chip memory configuration.
 * eflash virtual is a fixed address that does not physically exist but is used as the
 * translation base
 */
MEMORY {
  ram_ret_aon(rwx) : ORIGIN = 0x40600000, LENGTH = 0x1000
  ram_main(rwx) : ORIGIN = 0x10000000, LENGTH = 0x20000
  rom(rx) : ORIGIN = 0x00008000, LENGTH = 0x4000
  eflash(rx) : ORIGIN = 0x20000000, LENGTH = 0x100000
  eflash_virtual(rx) : ORIGIN = 0x80000000, LENGTH = 0x100000
}
