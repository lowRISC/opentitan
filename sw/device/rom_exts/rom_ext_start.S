// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

/**
 * ROM_EXT Interrupt Vector
 */
  .section .vectors, "ax"
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

/**
 * `_rom_ext_interrupt_vector` is an ibex-compatible interrupt vector.
 *
 * Interrupt vectors in Ibex have 32 entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * The ROM_EXT uses the address directly after the first possible interrupt
 * vector when starting execution after Mask ROM, which we choose to make look
 * like an extra entry. This is designed to match how Ibex chooses to implement
 * its initial execution address after boot.
 *
 * Thus this vector has exactly 33 4-byte entries.
 *
 * Only the following will be used by Ibex:
 * - Exception Handler (Entry 0)
 * - Machine Software Interrupt Handler (Entry 3)
 * - Machine Timer Interrupt Handler (Entry 7)
 * - Machine External Interrupt Handler (Entry 11)
 * - Vendor Interrupt Handlers (Entries 16-31)
 * - Reset Handler (Entry 32)
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/exception_interrupts.html
 */
  .balign 256
  .globl _rom_ext_interrupt_vector
  .type _rom_ext_interrupt_vector, @function
_rom_ext_interrupt_vector:

  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  unimp
  // Supervisor Software Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Software Interrupt Handler.
  unimp

  // User Timer Interrupt Handler.
  unimp
  // Supervisor Timer Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Timer Interrupt Handler.
  unimp

  // User External Interrupt Handler.
  unimp
  // Supervisor External Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine External Interrupt Handler.
  unimp

  // Reserved.
  unimp
  unimp
  unimp
  unimp

  // Vendor Interrupt Handlers:

  // On Ibex interrupt ids 30-16 are for "fast" interrupts.
  .rept 15
  unimp
  .endr

  // On Ibex interrupt id 31 is for non-maskable interrupts.
  unimp

  // Ibex Reset Handler:
  j _rom_ext_start_boot

  // Set size so this vector can be disassembled.
  .size _rom_ext_interrupt_vector, .-_rom_ext_interrupt_vector

  // Re-enable compressed instructions, linker relaxation.
  .option pop


/**
 * ROM_EXT runtime initialization code.
 */

  // NOTE: The "ax" flag below is necessary to ensure that this section
  // is allocated executable space in ROM by the linker.
  .section .crt, "ax"

  // Linker Relaxation is disabled until `__global_pointer$` is setup, below,
  // because otherwise some sequences may be turned into gp-relative sequences,
  // which is incorrect when `gp` is not initialized.
  .option push
  .option norelax

/**
 * Entry point after reset. This symbol is jumped to from the handler
 * for IRQ 32.
 *
 * At the moment, this should just fault, until we have a CRT we can use.
 */
  .globl _rom_ext_start_boot
  .type _rom_ext_start_boot, @function
_rom_ext_start_boot:
  unimp
