// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sram_start.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sw/device/lib/base/multibits_asm.h"

#include "csrng_regs.h"  // Generated.
#include "edn_regs.h"  // Generated.
#include "entropy_src_regs.h"  // Generated.

/**
 * SRAM Program Interrupt Vector.
 *
 * We reuse the OTTF interrupt handlers.
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
   * `sram_interrupt_vector` is an ibex-compatible interrupt vector.
   *
   * Interrupt vectors in Ibex have 32 4-byte entries for 32 possible interrupts.
   * The vector must be 256-byte aligned, as Ibex's vectoring mechanism requires
   * that.
   *
   * Only the following will be used by Ibex:
   * - Exception Handler (Entry 0)
   * - Machine Software Interrupt Handler (Entry 3)
   * - Machine Timer Interrupt Handler (Entry 7)
   * - Machine External Interrupt Handler (Entry 11)
   * - Vendor Interrupt Handlers (Entries 16-31)
   *
   * More information about Ibex's interrupts can be found here:
   *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
   */
  .balign 256
  .global sram_interrupt_vector
  .type sram_interrupt_vector, @function
sram_interrupt_vector:
  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  j handler_exception
  // Supervisor Software Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Software Interrupt Handler.
  j handler_irq_software

  // User Timer Interrupt Handler.
  unimp
  // Supervisor Timer Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Timer Interrupt Handler.
  j handler_irq_timer

  // User External Interrupt Handler.
  unimp
  // Supervisor External Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine External Interrupt Handler.
  j handler_irq_external

  // Reserved.
  unimp
  unimp
  unimp
  unimp

  // Vendor Interrupt Handlers:

  // On Ibex, interrupt IDs 16-30 are for "fast" interrupts.
  .rept 15
  unimp
  .endr

  // On Ibex, interrupt ID 31 is for non-maskable interrupts
  j handler_irq_internal

  // Set size so vector can be disassembled.
  .size sram_interrupt_vector, .-sram_interrupt_vector

  .option pop

/**
 * CRT library for SRAM programs.
 *
 * The purpose of this small library is to setup the stack pointer, global
 * pointer and clear the BSS. It will also verify the integrity with CRC32
 * and compare it with the host provided CRC32 data.
 *
 * @param a0 expected CRC32 value of the data between _crc_start and _crc_end.
 */

  .section .sram_start, "ax"
  .balign 4
  .global sram_start
  .type sram_start, @function
sram_start:

  // Set up the global pointer. This requires that we disable linker relaxations
  // (or it will be relaxed to `mv gp, gp`).
  .option push
  .option norelax
  la  gp, __global_pointer$
  .option pop

  // Save CRC32
  mv   sp, a0
  // Verify CRC
  la   a0, _crc_start
  la   a1, _crc_end
  call compute_crc32
  beq  a0, sp, .L_crc_match
  li   sp, SRAM_MAGIC_SP_CRC_ERROR
  ebreak

.L_crc_match:
  // Set up the stack.
  la  sp, _stack_end

  /**
   * Setup the interrupt/exception handlers.
   *
   * These are the same interrupt handlers used in the OTTF. The lowest two bits
   * should be `0b01` to ensure we use vectored interrupts.
   */
  la   t0, (sram_interrupt_vector + 1)
  csrw mtvec, t0

  // Zero out the `.bss` segment.
  la   a0, _bss_start
  la   a1, _bss_end
  call crt_section_clear

  // The following sequence enables the minimum level of entropy required to
  // initialize memory scrambling, as well as the entropy distribution network.
  // This enables writing to the SECRET* OTP partitions, required for
  // provisioning the test unlock/exit tokens.
  li a0, TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_FIPS_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_ENTROPY_DATA_REG_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_THRESHOLD_SCOPE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << ENTROPY_SRC_CONF_RNG_BIT_ENABLE_OFFSET)
  sw t0, ENTROPY_SRC_CONF_REG_OFFSET(a0)
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << ENTROPY_SRC_MODULE_ENABLE_MODULE_ENABLE_OFFSET)
  sw t0, ENTROPY_SRC_MODULE_ENABLE_REG_OFFSET(a0)
  li a0, TOP_EARLGREY_CSRNG_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_SW_APP_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << CSRNG_CTRL_READ_INT_STATE_OFFSET)
  sw t0, CSRNG_CTRL_REG_OFFSET(a0)
  li a0, TOP_EARLGREY_EDN0_BASE_ADDR
  li t0, (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_EDN_ENABLE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_TRUE << EDN_CTRL_BOOT_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_AUTO_REQ_MODE_OFFSET) | \
         (MULTIBIT_ASM_BOOL4_FALSE << EDN_CTRL_CMD_FIFO_RST_OFFSET)
  sw t0, EDN_CTRL_REG_OFFSET(a0)

  // Configure the AST
  li a0, 1
  call ast_program_config
  // Jump into the C program entry point.
  call sram_main

  // Notify the host that we are done.
  li  sp, SRAM_MAGIC_SP_EXECUTION_DONE
  ebreak

  // Set function size to allow disassembly.
  .size sram_start, .-sram_start

  /**
   * Compute the CRC32 of the section bounded by the start and end pointers.
   * The section must be word (4 byte) aligned.
   *
   * This function follows the standard ILP32 calling convention for arguments
   * but does not require a valid stack pointer, thread pointer or global
   * pointer.
   *
   * Clobbers a0, t0 and t1.
   *
   * @param a0 pointer to start of section to clear (inclusive).
   * @param a1 pointer to end of section to clear (exclusive).
   */
  .balign 4
  .global compute_crc32
  .type compute_crc32, @function
compute_crc32:
  // Check that start is before end.
  bgeu a0, a1, .L_crc_nothing

  // Check that start and end are word aligned.
  or   t0, a0, a1
  andi t0, t0, 0x3
  bnez t0, .L_crc_error
  // Initialize CRC digest.
  li   t0, 0xffffffff

.L_crc_loop:
  // Compute the CRC word-by-word.
  lw      t1, 0(a0)
  xor     t0, t0, t1
  .option push
  .option arch, +zbr0p93
  crc32.w t0, t0
  .option pop
  addi    a0, a0, 4
  bltu    a0, a1, .L_crc_loop

  // Finalize and return CRC
  li  t1, 0xffffffff
  xor a0, t0, t1
  ret

.L_crc_nothing:
  // If section length is 0 just return. Otherwise end is before start
  // which is invalid so trigger an error.
  bne a0, a1, .L_crc_error
  li  a0, 0
  ret

.L_crc_error:
  unimp

  // Set function size to allow disassembly.
  .size sram_start, .-sram_start
