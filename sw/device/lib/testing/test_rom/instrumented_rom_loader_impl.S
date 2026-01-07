// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sram_ctrl_regs.h"
#include "flash_ctrl_regs.h"

/**
 * Instrumented ROM loader.
 *
 * The loader checks if the instrumented ROM is present on flash, and if so,
 * it will configure the hardware to allow its execution. Then it jumps to the
 * instrumented ROM. Otherwise, it will fall back to the default test ROM by
 * just returning.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"
  .balign 4
  .global _try_instrumented_rom
  .type _try_instrumented_rom, @function

_try_instrumented_rom:
  /**
   * Unlock ePMP for Flash access
   */
  // Remove address space protections by configuring entry 15 as
  // read-write-execute for the entire address space and then clearing
  // all other entries.
  // NOTE: This should happen before attemting to access any address outside
  // the initial ePMP RX region at reset, e.g. `kDeviceType` which is in
  // .rodata.
  li   t0, (0x9f << 24) // Locked NAPOT read-write-execute.
  csrw pmpcfg3, t0
  li   t0, 0x7fffffff   // NAPOT encoded region covering entire 34-bit address space.
  csrw pmpaddr15, t0

  // Configure `pmpcfg0` in test ROM to enable instrumented ROM execution.
  // Without this configuration, the instrumented ROM can not be executed due to
  // ePMP reconfiguration in `rom_epmp_init`.
  li   t0, (0x8f << 8) // Locked TOR read-write-execute.
  csrw pmpcfg0, t0
  li   t0, 0
  csrw pmpaddr0, t0
  li   t0, 0x10000000 // TOR encoded region convering entire eFlash address space.
  csrw pmpaddr1, t0

  csrw pmpcfg1, zero
  csrw pmpcfg2, zero

  /**
   * Reset flash protection on the instrumented ROM region
   */
  li    t1, TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR

  // t0 = ( ((size / 2048) << 9) | (offset / 2048) )
  la    t0, _instrumented_rom_size
  srli  t0, t0, 11 // Divide by 2048 (2^11)
  slli  t0, t0, 9  // Shift to bit 9 for size field

  la    t3, _instrumented_rom_slot
  srli  t3, t3, 11 // Divide by 2048 (2^11)
  or    t0, t0, t3
  sw    t0, FLASH_CTRL_MP_REGION_7_REG_OFFSET(t1)

  // Enabled: Read / Write / Erase / Enable
  // Disabled: High Endurance / Scramble / ECC
  li t0, 0x9996666
  sw    t0, FLASH_CTRL_MP_REGION_CFG_7_REG_OFFSET(t1)

  /**
   * Check if instrumented ROM is presented
   */
  la a0, (_instrumented_rom_slot + TOP_EARLGREY_EFLASH_BASE_ADDR)

  // Continue test rom if the magic bytes are not 'IROM'
  // The magic bytes is defined in the `instrumented_header.c`.
  lw t0, 0x180(a0)
  li t1, 0x4d4f5249
  beq t0, t1, .L_boot_instrumented_rom
  ret

.L_boot_instrumented_rom:
  /**
   * Initialize the hardware for running instrumented ROM
   */
  // Initialize main memory (main SRAM).
  li    t1, TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  li    t0, (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw    t0, SRAM_CTRL_CTRL_REG_OFFSET(t1)

  // Set exception/interrupt handlers.
  //
  // Note: the increment just sets the low bits to 0b01 which is the vectored
  // mode setting.
  addi  t0, a0, 1
  csrw mtvec, t0

  // Unlock execution for code on the flash
  li   a3, TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR
  li   t1, 0xa26a38f7
  sw   t1, FLASH_CTRL_EXEC_REG_OFFSET(a3)

  /**
   * Jump to instrumented ROM
   */
  jr 0x80(a0)
  unimp

  .size _try_instrumented_rom, .-_try_instrumented_rom
