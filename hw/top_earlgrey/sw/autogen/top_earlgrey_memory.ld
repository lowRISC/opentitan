/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 * ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ------------------- *
 * PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
 * util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
 * -o hw/top_earlgrey
 */

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
  owner_virtual(rx) : ORIGIN = 0xa0000000, LENGTH = 0x80000
}

/**
 * Exception frame at the top of main SRAM
 */
_exception_frame_size = 128;
_exception_frame_end = ORIGIN(ram_main) + LENGTH(ram_main);
_exception_frame_start = _exception_frame_end - _exception_frame_size;


/**
 * Stack just below the exception frame.
 */
_stack_size = 16384 - _exception_frame_size;
_stack_end = _exception_frame_start;
_stack_start = _stack_end - _stack_size;

/**
 * Size of the `.static_critical` section at the bottom of the main SRAM (in
 * bytes).
 */
_static_critical_size = 8168;

/**
 * `.chip_info` at the top of each ROM.
 */
_chip_info_size = 128;
_rom_chip_info_end = ORIGIN(rom) + LENGTH(rom);
_rom_chip_info_start = _rom_chip_info_end - _chip_info_size;

/**
 * Size of the initial ePMP RX region at reset (in bytes). This region must be
 * large enough to cover the .crt section.
 *
 * NOTE: This value must match the size of the RX region in
 * hw/ip/rv_core_ibex/rtl/ibex_pmp_reset.svh.
 */
_epmp_reset_rx_size = 2048;
