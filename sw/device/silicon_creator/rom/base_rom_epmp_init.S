// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/epmp_defs.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling_memory.h"

/**
 * Helper macro to move v into the correct position to set the pmp{N*4+i}cfg
 * field in the pmpcfg{N} register.
 *
 * Example: set value for pmp5cfg which is a field of pmpcfg1.
 *
 *   li   t0, CFG_INDEX(5 % 4, v)
 *   csrw pmpcfg1, t0
 */
#define CFG_INDEX(i, v) ((v) << ((i)*8))

/**
 * Encode address for Top-Of-Range addressing mode.
 */
#define TOR(addr) ((addr) >> 2)

/**
 * Encode address and length for Naturally-Aligned-Power-Of-Two addressing
 * mode.
 */
#define NAPOT(addr, len) (((addr) >> 2) | (((len) - 1) >> 3))

// -----------------------------------------------------------------------------

  /**
   * The "ax" flag below is necessary to ensure that this section
   * is allocated space in ROM by the linker.
   */
  .section .crt, "ax", @progbits

  /**
   * Configure the CPU's Enhanced Physical Memory Protection (ePMP) feature.
   *
   * This function follows the standard ILP32 calling convention but does not
   * require a valid stack pointer, thread pointer or global pointer.
   *
   * May clobber temporary registers (t0-t6).
   */
  .balign 4
  .global base_rom_epmp_init
  .type base_rom_epmp_init, @function
base_rom_epmp_init:
  // Pre-encoded addresses defined in linker script.
  .extern _epmp_base_text_tor_lo
  .extern _epmp_base_text_tor_hi
  .extern _epmp_stack_guard_na4

  // Setup PMP address registers.

  // BASE ROM TEXT
  la   t0, _epmp_base_text_tor_lo
  csrw pmpaddr0, t0
  la   t0, _epmp_base_text_tor_hi
  csrw pmpaddr1, t0

  // BASE ROM
  li   t0, NAPOT(TOP_DARJEELING_ROM0_BASE_ADDR, TOP_DARJEELING_ROM0_SIZE_BYTES)
  csrw pmpaddr2, t0

  // unused in BASE ROM
  csrw pmpaddr3, zero
  csrw pmpaddr4, zero
  csrw pmpaddr5, zero

  // ROM1, will be configured just before jumping to it
  csrw pmpaddr6, zero
  csrw pmpaddr7, zero
  csrw pmpaddr8, zero

  // unused in BASE ROM
  csrw pmpaddr9, zero
  csrw pmpaddr10, zero

  // MMIO
  li   t0, TOR(TOP_DARJEELING_MMIO_BASE_ADDR)
  csrw pmpaddr11, t0
  li   t0, TOR(TOP_DARJEELING_MMIO_BASE_ADDR + TOP_DARJEELING_MMIO_SIZE_BYTES)
  csrw pmpaddr12, t0

  // Debug ROM
  li   t0, NAPOT(TOP_DARJEELING_RV_DM_MEM_BASE_ADDR, TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES)
  csrw pmpaddr13, t0

  // Stack guard
  la   t0, _epmp_stack_guard_na4
  csrw pmpaddr14, t0

  // RAM
  li   t0, NAPOT(TOP_DARJEELING_RAM_MAIN_BASE_ADDR, TOP_DARJEELING_RAM_MAIN_SIZE_BYTES)
  csrw pmpaddr15, t0

  // Set PMP configuration registers.
  li   t0, CFG_INDEX(1  % 4, EPMP_CFG_A_TOR   | EPMP_CFG_LRX) |  /* Base ROM TEXT         */ \
           CFG_INDEX(2  % 4, EPMP_CFG_A_NAPOT | EPMP_CFG_LR)     /* Base ROM              */
  li   t1, 0
  li   t2, 0
  li   t3, CFG_INDEX(12 % 4, EPMP_CFG_A_TOR   | EPMP_CFG_LRW) |  /* MMIO        */ \
           CFG_INDEX(13 % 4, EPMP_CFG_A_NAPOT | EPMP_CFG_LRWX)|  /* Debug ROM   */ \
           CFG_INDEX(14 % 4, EPMP_CFG_A_NA4   | EPMP_CFG_L)   |  /* Stack Guard */ \
           CFG_INDEX(15 % 4, EPMP_CFG_A_NAPOT | EPMP_CFG_LRW)    /* RAM         */
  csrw pmpcfg0, t0
  csrw pmpcfg1, t1
  csrw pmpcfg2, t2
  csrw pmpcfg3, t3

  ret
  .size base_rom_epmp_init, .-base_rom_epmp_init
