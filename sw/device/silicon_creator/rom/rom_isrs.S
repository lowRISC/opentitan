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
  // Save all registers to an exception stack.  The ROM locates its initial
  // stack at `ram_end - 16` and the stack grows downwards from there, leaving
  // 16 bytes at the top of RAM.  We need exactly 16 bytes to handle the flash
  // exception, so we save `sp` into `mscratch` and use those 16 bytes to save
  // the 4 registers we need to handle the flash exception.
  csrw mscratch, sp
  la   sp, (_stack_end - 16)
  sw   a0,  0 * OT_WORD_SIZE(sp)
  sw   a1,  1 * OT_WORD_SIZE(sp)
  sw   a2,  2 * OT_WORD_SIZE(sp)
  sw   a3,  3 * OT_WORD_SIZE(sp)

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


// The following two macros help build an if/else tree to load the
// correct register with zero.
#define LOAD_ZERO_INTO_REG(reg_) \
  addi a3, a3, -1; \
  bnez a3, 1f; \
  mv   reg_, a2; \
  j    .L_flash_fault_done; \
  1:

#define LOAD_ZERO_STACK_REG(reg_) \
  addi a3, a3, -1; \
  bnez a3, 1f; \
  sw   a2, reg_ * OT_WORD_SIZE(sp); \
  j    .L_flash_fault_done; \
  1:

  // Now, using `rd` from the faulting instruction (in a3), load a zero into
  // that register.
  // RISCV register x0, aka zero.  This register is always const 0, so there
  // is nothing to do.
  beqz a3, .L_flash_fault_done

  // All other register load the value 0xFFFFFFFF as the faulting value.
  li   a2, -1
  LOAD_ZERO_INTO_REG(x1)   // Register x1 aka ra
  LOAD_ZERO_INTO_REG(x2)   // Register x2 aka sp
  LOAD_ZERO_INTO_REG(x3)   // Register x3 aka gp
  LOAD_ZERO_INTO_REG(x4)   // Register x4 aka tp
  LOAD_ZERO_INTO_REG(x5)   // Register x5 aka t0
  LOAD_ZERO_INTO_REG(x6)   // Register x6 aka t1
  LOAD_ZERO_INTO_REG(x7)   // Register x7 aka t2
  LOAD_ZERO_INTO_REG(x8)   // Register x8 aka s0
  LOAD_ZERO_INTO_REG(x9)   // Register x9 aka s1
  LOAD_ZERO_STACK_REG(0)   // Register x10 aka a0
  LOAD_ZERO_STACK_REG(1)   // Register x11 aka a1
  LOAD_ZERO_STACK_REG(2)   // Register x12 aka a2
  LOAD_ZERO_STACK_REG(3)   // Register x13 aka a3
  LOAD_ZERO_INTO_REG(x14)  // Register x14 aka a4
  LOAD_ZERO_INTO_REG(x15)  // Register x15 aka a5
  LOAD_ZERO_INTO_REG(x16)  // Register x16 aka a6
  LOAD_ZERO_INTO_REG(x17)  // Register x17 aka a7
  LOAD_ZERO_INTO_REG(x18)  // Register x18 aka s2
  LOAD_ZERO_INTO_REG(x19)  // Register x19 aka s3
  LOAD_ZERO_INTO_REG(x20)  // Register x20 aka s4
  LOAD_ZERO_INTO_REG(x21)  // Register x21 aka s5
  LOAD_ZERO_INTO_REG(x22)  // Register x22 aka s6
  LOAD_ZERO_INTO_REG(x23)  // Register x23 aka s7
  LOAD_ZERO_INTO_REG(x24)  // Register x24 aka s8
  LOAD_ZERO_INTO_REG(x25)  // Register x25 aka s9
  LOAD_ZERO_INTO_REG(x26)  // Register x26 aka s10
  LOAD_ZERO_INTO_REG(x27)  // Register x27 aka s11
  LOAD_ZERO_INTO_REG(x28)  // Register x28 aka t3
  LOAD_ZERO_INTO_REG(x29)  // Register x29 aka t4
  LOAD_ZERO_INTO_REG(x30)  // Register x30 aka t5
  LOAD_ZERO_INTO_REG(x31)  // Register x31 aka t6

.L_flash_fault_done:
  // Exception handler exit and return to C:
  // Load the correct MEPC for the next instruction in the current task.
  csrw mepc, a0

  // Restore all registers from the stack and restore SP to its former value.
  lw   a0,  0 * OT_WORD_SIZE(sp)
  lw   a1,  1 * OT_WORD_SIZE(sp)
  lw   a2,  2 * OT_WORD_SIZE(sp)
  lw   a3,  3 * OT_WORD_SIZE(sp)
  csrr sp, mscratch
  mret

.L_not_a_flash_error:
  // Since we aren't dealing with a flash error, we'll jump to the normal
  // handler for all other exceptiosn and interrupts.  That handler emits
  // the fault info to the UART and initiates shutdown.  No register state
  // preservation is necessary because we're not coming back.
  //
  // Note: we _also_ do not restore SP - we'll restart the stack at
  // `ram_end - 16`.  This allows us to report exceptions after jumping
  // to the next stage if the next stage has trashed its SP register.
  j rom_interrupt_handler
  unimp
  unimp

  .size rom_exception_handler, .-rom_exception_handler
