// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sw/device/lib/base/macros.h"
#include "flash_ctrl_regs.h"

.equ LOAD_ACCESS_FAULT, 5

// If we get an ECC error reading from internal flash, one of these bits
// will be set in the flash controller's FAULT_STATUS register.
.equ PHY_ERRORS, (1 << FLASH_CTRL_FAULT_STATUS_PHY_STORAGE_ERR_BIT) | \
                 (1 << FLASH_CTRL_FAULT_STATUS_PHY_RELBL_ERR_BIT)

// NOTE: The "ax" flag below is necessary to ensure that this section
// is allocated executable space in ROM by the linker.
.section .rom_isrs, "ax"

// -----------------------------------------------------------------------------

  /**
   * Exception handler.
   */
  .balign 4
  .global rom_exception_handler
  .type rom_exception_handler, @function
rom_exception_handler:
  // Save all registers to the exception frame.  The ROM locates its initial
  // stack_end at `ram_end - 128` and the stack grows downwards from there.
  // Save `sp` into `mscratch` and use the 128 bytes reserved at the top of
  // RAM as the exception frame.
  csrw mscratch, sp
  la   sp,  _exception_frame_start
  sw   t0,  0 * OT_WORD_SIZE(sp)
  sw   t1,  1 * OT_WORD_SIZE(sp)
  sw   t2,  2 * OT_WORD_SIZE(sp)
  sw   t3,  3 * OT_WORD_SIZE(sp)

  /**
   * Compute the MEPC of the instruction after the fault.
   *
   * Since we support the RISC-V compressed instructions extension, we need to
   * check if the two least significant bits of the instruction are
   * b11 (0x3), which means that the trapped instruction is not compressed,
   * i.e., the trapped instruction is 32bits = 4bytes. Otherwise, the trapped
   * instruction is 16bits = 2bytes.
   */
  csrr t0, mepc
  lh t2, 0(t0)
  addi t0, t0, OT_HALF_WORD_SIZE
  li t1, 0x3
  and t3, t2, t1
  bne t3, t1, .L_rom_16bit_trap_instr
  // We already added one half word, so for a 32-bit instruction, add another.
  addi t0, t0, OT_HALF_WORD_SIZE
.L_rom_16bit_trap_instr:
  // Hardening: double-check that the retval calculation is 4 bytes or fewer
  // from the original value of MEPC.
  addi t1, t1, 1
  csrr t2, mepc
  sub t2, t0, t2
  bgtu t2, t1, .L_not_a_flash_error

  // Get the mcause, mask the reason and check that it is LoadAccessFault.
  csrr t1, mcause
  andi t1, t1, 31
  li t2, LOAD_ACCESS_FAULT
  bne t1, t2, .L_not_a_flash_error

  // Check if there is a flash error.
  li t3, TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR
  lw t1, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(t3)
  andi t1, t1, PHY_ERRORS
  beqz t1, .L_not_a_flash_error

  // Clear the flash error.
  sw x0, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(t3)
  // Hardening: check that the error is cleared.
  lw t1, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(t3)
  beqz t1, .L_flash_fault_handled
  j .L_not_a_flash_error
  unimp
  unimp

.L_flash_fault_handled:
  // Exception handler exit and return to C:
  // Load the correct MEPC for the next instruction in the current task.
  csrw mepc, t0

  // Restore all registers from the stack and restore SP to its former value.
  lw   t0,  0 * OT_WORD_SIZE(sp)
  lw   t1,  1 * OT_WORD_SIZE(sp)
  lw   t2,  2 * OT_WORD_SIZE(sp)
  lw   t3,  3 * OT_WORD_SIZE(sp)
  csrr sp, mscratch
  mret

.L_not_a_flash_error:
  // Since we aren't dealing with a flash error, we'll jump to the normal
  // handler for all other exceptiosn and interrupts.  That handler emits
  // the fault info to the UART and initiates shutdown.  No register state
  // preservation is necessary because we're not coming back.
  //
  // Note: we _also_ do not restore SP - we'll restart the stack at
  // `ram_end - 128`.  This allows us to report exceptions after jumping
  // to the next stage if the next stage has trashed its SP register.
  j rom_interrupt_handler
  unimp
  unimp

  .size rom_exception_handler, .-rom_exception_handler
