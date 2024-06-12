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
  // Note: we save the exception frame in RISCV register number order so that
  // we can extract the destination register from the faulting instruction and
  // use it as an index into the exception frame.
  csrw mscratch, sp
  la   sp, _exception_frame_start
  sw   x1,  1 * OT_WORD_SIZE(sp)
  sw   x2,  2 * OT_WORD_SIZE(sp)
  sw   x3,  3 * OT_WORD_SIZE(sp)
  sw   x4,  4 * OT_WORD_SIZE(sp)
  sw   x5,  5 * OT_WORD_SIZE(sp)
  sw   x6,  6 * OT_WORD_SIZE(sp)
  sw   x7,  7 * OT_WORD_SIZE(sp)
  sw   x8,  8 * OT_WORD_SIZE(sp)
  sw   x9,  9 * OT_WORD_SIZE(sp)
  sw   x10,  10 * OT_WORD_SIZE(sp)
  sw   x11,  11 * OT_WORD_SIZE(sp)
  sw   x12,  12 * OT_WORD_SIZE(sp)
  sw   x13,  13 * OT_WORD_SIZE(sp)
  sw   x14,  14 * OT_WORD_SIZE(sp)
  sw   x15,  15 * OT_WORD_SIZE(sp)
  sw   x16,  16 * OT_WORD_SIZE(sp)
  sw   x17,  17 * OT_WORD_SIZE(sp)
  sw   x18,  18 * OT_WORD_SIZE(sp)
  sw   x19,  19 * OT_WORD_SIZE(sp)
  sw   x20,  20 * OT_WORD_SIZE(sp)
  sw   x21,  21 * OT_WORD_SIZE(sp)
  sw   x22,  22 * OT_WORD_SIZE(sp)
  sw   x23,  23 * OT_WORD_SIZE(sp)
  sw   x24,  24 * OT_WORD_SIZE(sp)
  sw   x25,  25 * OT_WORD_SIZE(sp)
  sw   x26,  26 * OT_WORD_SIZE(sp)
  sw   x27,  27 * OT_WORD_SIZE(sp)
  sw   x28,  28 * OT_WORD_SIZE(sp)
  sw   x29,  29 * OT_WORD_SIZE(sp)
  sw   x30,  30 * OT_WORD_SIZE(sp)
  sw   x31,  31 * OT_WORD_SIZE(sp)

  // Get the mcause, mask the reason and check that it is LoadAccessFault.
  csrr a1, mcause
  andi a1, a1, 31
  li   a2, LOAD_ACCESS_FAULT
  bne  a1, a2, .L_not_a_flash_error

  // Check if there is a flash error.
  li   a3, TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR
  lw   a1, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(a3)
  andi a1, a1, PHY_ERRORS
  beqz a1, .L_not_a_flash_error

  // Clear the flash error.
  sw   x0, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(a3)
  // Hardening: check that the error is cleared.
  lw   a1, FLASH_CTRL_FAULT_STATUS_REG_OFFSET(a3)
  beqz a1, .L_flash_fault_handled
  j    .L_not_a_flash_error
  unimp
  unimp

.L_flash_fault_handled:
  // Compute the MEPC of the instruction after the fault.
  //
  // Since we support the RISC-V compressed instructions extension, we need to
  // check if the two least significant bits of the instruction are
  // b11 (0x3), which means that the trapped instruction is not compressed,
  // i.e., the trapped instruction is 32bits = 4bytes. Otherwise, the trapped
  // instruction is 16bits = 2bytes.
  //
  // Instruction formats for loads:
  //
  //  LB, LH, LW, LBU, LHU:
  //  31                  20 19      15 14  12 11       7 6            0
  // +----------------------+----------+------+----------+--------------+
  // |      imm[11:0]       |    rs1   |funct3|    rd    |   0000011    |
  // +----------------------+----------+------+----------+--------------+
  //
  // C.LW
  //  15  13 12  10 9    7 6  5 4    2 1  0
  // +------+------+------+----+------+----+
  // |funct3| imm  | rs1' | imm|  rd' | 00 |
  // +------+------+------+----+------+----+
  // Where rd' and rs1' are (register_num - 8, ie: rd' of 0 means reg x8).
  //

  csrr a0, mepc
  lh   a2, 0(a0)
  addi a0, a0, OT_HALF_WORD_SIZE
  // Check if its a 16-bit compressed instruction.
  li   a1, 3
  and  a3, a2, a1
  bne  a3, a1, .L_compressed_trap_instr
  // Check if its an uncompressed load instruction by checking that the next
  // five bits are zero.
  srli a3, a2, 2
  andi a3, a3, 0x1f
  bnez a3, .L_not_a_flash_error
  // Get the register number into a3 by masking off the rd field.
  srli a3, a2, 7
  andi a3, a3, 0x1f
  // We already added one half word, so for a 32-bit instruction, add another.
  addi a0, a0, OT_HALF_WORD_SIZE
  j    .L_hardened_mepc_check

.L_compressed_trap_instr:
  // Check if its a compressed load instruction.
  bnez a3, .L_not_a_flash_error
  // Get the register number into a3 by masking off the rd' field and adding 8.
  srli a3, a2, 2
  andi a3, a3, 7
  addi a3, a3, 8

.L_hardened_mepc_check:
  // Hardening: double-check that the retval calculation is 4 bytes or fewer
  // from the original value of MEPC.
  addi a1, a1, 1
  csrr a2, mepc
  sub  a2, a0, a2
  bgtu a2, a1, .L_not_a_flash_error

  // Now, using `rd` from the faulting instruction (in a3), load all ones into
  // that register.
  // RISCV register x0, aka zero.  This register is always const 0, so there
  // is nothing to do.
  beqz a3, .L_flash_fault_done

  // All other registers load the value 0xFFFFFFFF as the faulting value.
  li   a2, -1
  slli a3, a3, 2
  add  a3, a3, sp
  sw   a2, 0(a3)

.L_flash_fault_done:
  // Exception handler exit and return to C:
  // Load the correct MEPC for the next instruction in the current task.
  csrw mepc, a0

  // Restore all registers from the stack and restore SP to its former value.
  lw   x1,  1 * OT_WORD_SIZE(sp)
  lw   x2,  2 * OT_WORD_SIZE(sp)
  lw   x3,  3 * OT_WORD_SIZE(sp)
  lw   x4,  4 * OT_WORD_SIZE(sp)
  lw   x5,  5 * OT_WORD_SIZE(sp)
  lw   x6,  6 * OT_WORD_SIZE(sp)
  lw   x7,  7 * OT_WORD_SIZE(sp)
  lw   x8,  8 * OT_WORD_SIZE(sp)
  lw   x9,  9 * OT_WORD_SIZE(sp)
  lw   x10,  10 * OT_WORD_SIZE(sp)
  lw   x11,  11 * OT_WORD_SIZE(sp)
  lw   x12,  12 * OT_WORD_SIZE(sp)
  lw   x13,  13 * OT_WORD_SIZE(sp)
  lw   x14,  14 * OT_WORD_SIZE(sp)
  lw   x15,  15 * OT_WORD_SIZE(sp)
  lw   x16,  16 * OT_WORD_SIZE(sp)
  lw   x17,  17 * OT_WORD_SIZE(sp)
  lw   x18,  18 * OT_WORD_SIZE(sp)
  lw   x19,  19 * OT_WORD_SIZE(sp)
  lw   x20,  20 * OT_WORD_SIZE(sp)
  lw   x21,  21 * OT_WORD_SIZE(sp)
  lw   x22,  22 * OT_WORD_SIZE(sp)
  lw   x23,  23 * OT_WORD_SIZE(sp)
  lw   x24,  24 * OT_WORD_SIZE(sp)
  lw   x25,  25 * OT_WORD_SIZE(sp)
  lw   x26,  26 * OT_WORD_SIZE(sp)
  lw   x27,  27 * OT_WORD_SIZE(sp)
  lw   x28,  28 * OT_WORD_SIZE(sp)
  lw   x29,  29 * OT_WORD_SIZE(sp)
  lw   x30,  30 * OT_WORD_SIZE(sp)
  lw   x31,  31 * OT_WORD_SIZE(sp)
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

  // Normally, we'd put an `unimp` sled here, however, we know by inspecting
  // the disassembly of the linked ROM binary that the very next instruction
  // is the beginning of `rom_interrupt_handler`.
  .size rom_exception_handler, .-rom_exception_handler
