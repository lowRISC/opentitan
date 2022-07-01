/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Partial linker script for chip memory configuration.
 * rom_ext_virtual and owner_virtual are address windows that provide a fixed translation
 * address for whichever half of the flash contains the corresponding boot stage.
 */
MEMORY {
  ram_ret_aon(rwx) : ORIGIN = 0x40600000, LENGTH = 0x1000
  eflash(rx) : ORIGIN = 0x20000000, LENGTH = 0x100000
  ram_main(rwx) : ORIGIN = 0x10000000, LENGTH = 0x20000
  rom(rx) : ORIGIN = 0x00008000, LENGTH = 0x8000
  rom_ext_virtual(rx) : ORIGIN = 0x90000000, LENGTH = 0x80000
  owner_virtual(rx): ORIGIN = 0xa0000000, LENGTH = 0x80000
}
