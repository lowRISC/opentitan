// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/multibits_asm.h"
#include "hw/top/rv_core_ibex_regs.h"  // Generated.
#include "hw/top/sram_ctrl_regs.h"  // Generated.
#include "hw/top/top_memory.h" // Generated.
#include "hw/top/uart_regs.h"  // Generated.

#define MISA_E (1 << 4)
#define MISA_I (1 << 8)
#define MISA_MODE (MISA_E | MISA_I)

#define MSTATUS_MIE (1 << 3)
#define CPUCTRL_DUMMY_INSTR_EN (1 << 2)

#define SWITCH_POLL_LIMIT 0x1000

#define SRAM_CTRL_STATUS_ERRORS                                            \
  ((1 << SRAM_CTRL_STATUS_BUS_INTEG_ERROR_BIT) |                           \
   (1 << SRAM_CTRL_STATUS_INIT_ERROR_BIT) |                                \
   (1 << SRAM_CTRL_STATUS_ESCALATED_BIT) |                                 \
   (1 << SRAM_CTRL_STATUS_READBACK_ERROR_BIT) |                            \
   (1 << SRAM_CTRL_STATUS_SRAM_ALERT_BIT))

#define DV_STATUS_IN_TEST 0x4354
#define DV_STATUS_PASSED 0x900d
#define DV_STATUS_FAILED 0xbaad

// Write the character `ch` to UART pointed to by register `uart_ptr`.
// Uses `temp` as a temporary clobber register.
.macro putc uart_ptr, temp, ch
1:
  lw   \temp, UART_STATUS_REG_OFFSET(\uart_ptr)
  andi \temp, \temp, (1 << UART_STATUS_TXFULL_BIT)
  bnez \temp, 1b
  li   \temp, \ch
  sw   \temp, UART_WDATA_REG_OFFSET(\uart_ptr)
.endm

// Write the character held in register `reg` to UART pointed to by register `uart_ptr`.
// Uses `temp` as a temporary clobber register.
.macro putr uart_ptr, temp, reg
1:
  lw   \temp, UART_STATUS_REG_OFFSET(\uart_ptr)
  andi \temp, \temp, (1 << UART_STATUS_TXFULL_BIT)
  bnez \temp, 1b
  sw   \reg, UART_WDATA_REG_OFFSET(\uart_ptr)
.endm

// Write the value of the register `reg` to UART pointed to by register `uart_ptr`
// as a string of hexadecimal digits.
// Uses `temp1` and `temp2` as temporary clobber registers.
.macro puthex uart_ptr, temp1, temp2, reg
.irp nibble, 0, 1, 2, 3, 4, 5, 6, 7
  // temp1 contains the current nibble.
  slli \temp1, \reg, (\nibble * 4)
  srli \temp1, \temp1, (32 - 4)
  // If less than 10, then the nibble is a digit 0-9, so add '0'.
  // Otherwise, the nibble is a digit a-f, so add 'a', and subtract 10.
  li   \temp2, 10
  blt  \temp1, \temp2, 2f
  addi \temp1, \temp1, ('a' - '0' - 10)
2:
  addi \temp1, \temp1, '0'
  putr \uart_ptr, \temp2, \temp1
.endr
.endm

// Write the address and metadata of a capability register `reg` to UART pointed to
// by `uart_ptr` as two strings of hexadecimal digits separated by a '-'.
// Uses `temp1`, `temp2`, and `temp3` as temporary clobber registers.
.macro putcap uart_ptr, temp1, temp2, temp3, reg
  cgetaddr \temp3, \reg
  puthex   \uart_ptr, \temp1, \temp2, \temp3
  putc     \uart_ptr, \temp1, '-'
  cgethigh \temp3, \reg
  puthex   \uart_ptr, \temp1, \temp2, \temp3
.endm

// Spin at this point until the host writes a non-zero value to register `reg`,
// also defining the label `label` so that a testbench can wait for the
// PC to reach here.
.macro wait_here_for_host label, reg
  li \reg, 0
  .globl \label
\label:
  beqz \reg, \label
.endm

 // Write `value` to the DV test status window.
 // Uses `temp1`, `temp2` as temporary clobber registers.
.macro dv_status temp1, temp2, value
#ifdef DV_TEST_STATUS
  csrr \temp1, misa
  andi \temp1, \temp1, MISA_E
  li   \temp2, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  beqz \temp1, 1f
  cspecialr c\temp1, mtdc
  csetaddr  c\temp2, c\temp1, \temp2
1:
  li   \temp1, \value
  sw   \temp1, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(\temp2)
#endif
.endm

  .section .crt, "ax", @progbits
  .balign 4
  .globl _ottf_start
  .type _ottf_start, @function
_ottf_start:
  .option push
  .option norvc
  .option norelax
  .option arch, rv32i_zicsr

  // Disable all interrupts.
  csrci mstatus, MSTATUS_MIE
  csrw  mie, x0

  // Disable dummy instructions.
  csrci CSR_REG_CPUCTRL, CPUCTRL_DUMMY_INSTR_EN

  // Setup trap handler.
  lui  t0, %hi(_trap_handler)
  addi t0, t0, %lo(_trap_handler)
  csrw mtvec, t0
  dv_status t0, t1, DV_STATUS_IN_TEST

  // Indicate we are ready for host harness to connect.
  li   x1, TOP_UART0_BASE_ADDR
  .irp ch, 'D','M',' ','R','E','A','D','Y','\r','\n'
  putc x1, x2, \ch
  .endr
  // Wait here for the host harness to connect and
  // write x1 with a non-zero value.
  wait_here_for_host wait_initial_attach, x1

  // We need at least one register to spin on and a few clobbers,
  // so to test reading and writing the GPRs over the Debug Module,
  // we perform this sequence twice - first to test registers x0-x15,
  // then x16-x31. In each case the other registers are used for
  // UART output, pointers, clobbers, etc. 'x' names are used instead
  // of ABI names for readability.

test_rv32_gprs_low:
  // Test GPRs x0-x15.
  // x16 - Wait for this register to be written before continuing.
  // x17 - UART address.
  // x18 - Pointer to register values to send and load.
  // x19, x20, x21 - Clobbers.
  li   x17, TOP_UART0_BASE_ADDR
  lui  x18, %hi(test_registers)
  addi x18, x18, %lo(test_registers)
  .irp ch, 'V','A','L','U','E','S',' ','x','0','-','x','1','5','\r','\n'
  putc x17, x19, \ch
  .endr

  puthex x17, x20, x21, x0
  putc   x17, x19, '\r'
  putc   x17, x19, '\n'
  .irp i, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
  lw     x19, (4 * \i)(x18)
  puthex x17, x20, x21, x19
  putc   x17, x19, '\r'
  putc   x17, x19, '\n'
  .endr

  lw x1, (4 * 1)(x18)
  lw x2, (4 * 2)(x18)
  lw x3, (4 * 3)(x18)
  lw x4, (4 * 4)(x18)
  lw x5, (4 * 5)(x18)
  lw x6, (4 * 6)(x18)
  lw x7, (4 * 7)(x18)
  lw x8, (4 * 8)(x18)
  lw x9, (4 * 9)(x18)
  lw x10, (4 * 10)(x18)
  lw x11, (4 * 11)(x18)
  lw x12, (4 * 12)(x18)
  lw x13, (4 * 13)(x18)
  lw x14, (4 * 14)(x18)
  lw x15, (4 * 15)(x18)

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x17, x19, \ch
  .endr
  wait_here_for_host wait_rv32_first, x16

test_rv32_gprs_high:
  // Test GPRs x16-x31.
  // x1 - Wait for this register to be written before continuing.
  // x2 - UART address.
  // x3 - Pointer to register values to send and load.
  // x4, x5, x6 - Clobbers.
  li   x2, TOP_UART0_BASE_ADDR
  lui  x3, %hi(test_registers)
  addi x3, x3, %lo(test_registers)
  .irp ch, 'V','A','L','U','E','S',' ','x','1','6','-','x','3','1','\r','\n'
  putc x2, x4, \ch
  .endr

  .irp i, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
  lw     x4, (4 * \i)(x3)
  puthex x2, x5, x6, x4
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'
  .endr

  lw x16, (4 * 0)(x3)
  lw x17, (4 * 1)(x3)
  lw x18, (4 * 2)(x3)
  lw x19, (4 * 3)(x3)
  lw x20, (4 * 4)(x3)
  lw x21, (4 * 5)(x3)
  lw x22, (4 * 6)(x3)
  lw x23, (4 * 7)(x3)
  lw x24, (4 * 8)(x3)
  lw x25, (4 * 9)(x3)
  lw x26, (4 * 10)(x3)
  lw x27, (4 * 11)(x3)
  lw x28, (4 * 12)(x3)
  lw x29, (4 * 13)(x3)
  lw x30, (4 * 14)(x3)
  lw x31, (4 * 15)(x3)

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x2, x4, \ch
  .endr
  wait_here_for_host wait_rv32_second, x1

test_rv32_csrs:
  // Test some writable CSRs.
  li   x2, TOP_UART0_BASE_ADDR
  .irp ch, 'V','A','L','U','E','S',' ','C','S','R','s','\r','\n'
  putc x2, x4, \ch
  .endr

  lui    x3, %hi(test_rv32_mscratch)
  addi   x3, x3, %lo(test_rv32_mscratch)
  lw     x3, 0(x3)
  csrw   mscratch, x3
  puthex x2, x4, x5, x3
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'

  lui    x3, %hi(test_rv32_mepc)
  addi   x3, x3, %lo(test_rv32_mepc)
  lw     x3, 0(x3)
  csrw   mepc, x3
  puthex x2, x4, x5, x3
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'

  lui    x3, %hi(test_rv32_mtval)
  addi   x3, x3, %lo(test_rv32_mtval)
  lw     x3, 0(x3)
  csrw   mtval, x3
  puthex x2, x4, x5, x3
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'

  csrr   x3, mtvec
  puthex x2, x4, x5, x3
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x2, x4, \ch
  .endr
  wait_here_for_host wait_rv32_third, x1

.option pop

enable_cheriot_mode:
  // Switch from RV32 to CHERIoT mode.

  // Zero-initialise the meta SRAM.
  li   a0, TOP_SRAM_CTRL_META_REGS_BASE_ADDR
  li   t0, (1 << SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT) | \
           (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw   t0, SRAM_CTRL_CTRL_REG_OFFSET(a0)
.L_meta_init_wait:
  lw   t0, SRAM_CTRL_STATUS_REG_OFFSET(a0)
  andi t1, t0, SRAM_CTRL_STATUS_ERRORS
  bnez t1, _trap_handler
  andi t1, t0, (1 << SRAM_CTRL_STATUS_INIT_DONE_BIT)
  beqz t1, .L_meta_init_wait

  // Lock re-keying of meta SRAM.
  sw x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(a0)
  li a0, TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  sw x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(a0)
  li a0, TOP_SRAM_CTRL_SEC_REGS_BASE_ADDR
  sw x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(a0)

  // x16-x31 hold the capability metadata of x0-x15 in CHERIoT mode, so zero
  // them ahead of the mode switch.
  .option push
  .option arch, rv32i_zicsr
  .irp reg, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31
  li \reg, 0
  .endr
  .option pop

  li  t0, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  li  t1, MULTIBIT_ASM_BOOL4_TRUE
  sw  t1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(t0)
  lw  t2, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(t0)
  bne t2, t1, _fail_ena
  li  t2, SWITCH_POLL_LIMIT
  sw  t1, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(t0)
  fence.i
  fence

.L_switch_wait:
  csrr t0, misa
  andi t0, t0, MISA_E
  bnez t0, .L_switched
  addi t2, t2, -1
  bnez t2, .L_switch_wait
  j    _fail_switch
.L_switched:

  cspecialr     x1, mtdc
  li            x2, TOP_UART0_BASE_ADDR
  csetaddr      x2, x1, x2
  csetboundsimm x2, x2, TOP_UART0_SIZE_BYTES

  .irp ch, 'C','H','E','R','I','o','T',' ','R','E','A','D','Y','\r','\n'
  putc x2, x3, \ch
  .endr

  wait_here_for_host wait_cheriot_first, x1

test_cheriot_gprs_low:
  // Test CHERIoT GPRs x0-x7.
  // x8 - Wait for this register to be written before continuing.
  // x9 - UART capability pointer.
  // x10 - Capability pointer to capability values to send and load.
  // x11, x12, x13, x14 - Clobbers.
  cspecialr     x11, mtdc
  li            x9, TOP_UART0_BASE_ADDR
  csetaddr      x9, x11, x9
  csetboundsimm x9, x9, TOP_UART0_SIZE_BYTES
  lui           x10, %hi(test_capabilities)
  addi          x10, x10, %lo(test_capabilities)
  csetaddr      x10, x11, x10

  .irp ch, 'V','A','L','U','E','S',' ','c','0','-','c','7','\r','\n'
  putc x9, x11, \ch
  .endr

  putcap x9, x11, x12, x13, x0
  putc   x9, x11, '\r'
  putc   x9, x11, '\n'
  .irp i, 1, 2, 3, 4, 5, 6, 7
  clc    x14, (8 * \i)(x10)
  putcap x9, x11, x12, x13, x14
  putc   x9, x11, '\r'
  putc   x9, x11, '\n'
  .endr

  lc x1, (8 * 1)(x10)
  lc x2, (8 * 2)(x10)
  lc x3, (8 * 3)(x10)
  lc x4, (8 * 4)(x10)
  lc x5, (8 * 5)(x10)
  lc x6, (8 * 6)(x10)
  lc x7, (8 * 7)(x10)

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x9, x11, \ch
  .endr

  wait_here_for_host wait_cheriot_second, x8

test_cheriot_gprs_high:
  // Test CHERIoT GPRs x8-x15.
  // x1 - Wait for this register to be written before continuing.
  // x2 - UART capability pointer.
  // x3 - Capability pointer to capability values to send and load.
  // x4, x5, x6, x7 - Clobbers.
  cspecialr     x4, mtdc
  li            x2, TOP_UART0_BASE_ADDR
  csetaddr      x2, x4, x2
  csetboundsimm x2, x2, TOP_UART0_SIZE_BYTES
  lui           x3, %hi(test_capabilities)
  addi          x3, x3, %lo(test_capabilities)
  csetaddr      x3, x4, x3

  .irp ch, 'V','A','L','U','E','S',' ','c','8','-','c','1','5','\r','\n'
  putc x2, x4, \ch
  .endr

  .irp i, 8, 9, 10, 11, 12, 13, 14, 15
  clc    x7, (8 * \i)(x3)
  putcap x2, x4, x5, x6, x7
  putc   x2, x4, '\r'
  putc   x2, x4, '\n'
  .endr

  lc x8, (8 * 8)(x3)
  lc x9, (8 * 9)(x3)
  lc x10, (8 * 10)(x3)
  lc x11, (8 * 11)(x3)
  lc x12, (8 * 12)(x3)
  lc x13, (8 * 13)(x3)
  lc x14, (8 * 14)(x3)
  lc x15, (8 * 15)(x3)

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x2, x4, \ch
  .endr

  wait_here_for_host wait_cheriot_third, x1

test_cheriot_scrs_csrs:
  // Test some writable SCRs and CSRs.
  cspecialr     x4, mtdc
  li            x2, TOP_UART0_BASE_ADDR
  csetaddr      x2, x4, x2
  csetboundsimm x2, x2, TOP_UART0_SIZE_BYTES
  .irp ch, 'V','A','L','U','E','S',' ','S','C','R','s','\r','\n'
  putc x2, x5, \ch
  .endr

  lui       x3, %hi(test_cheriot_mscratchc)
  addi      x3, x3, %lo(test_cheriot_mscratchc)
  csetaddr  x3, x4, x3
  clc       x3, 0(x3)
  cspecialw mscratchc, x3
  putcap    x2, x5, x6, x7, x3
  putc      x2, x5, '\r'
  putc      x2, x5, '\n'

  lui       x3, %hi(test_cheriot_mepcc)
  addi      x3, x3, %lo(test_cheriot_mepcc)
  csetaddr  x3, x4, x3
  clc       x3, 0(x3)
  cspecialw mepcc, x3
  putcap    x2, x5, x6, x7, x3
  putc      x2, x5, '\r'
  putc      x2, x5, '\n'

  lui      x3, %hi(test_cheriot_mtval)
  addi     x3, x3, %lo(test_cheriot_mtval)
  csetaddr x3, x4, x3
  lw       x3, 0(x3)
  csrw     mtval, x3
  puthex   x2, x5, x6, x3
  putc     x2, x5, '\r'
  putc     x2, x5, '\n'

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x2, x5, \ch
  .endr
  wait_here_for_host wait_cheriot_fourth, x1

test_cheriot_cap_tags_gprs:
  // Load some valid capabilities into GPRs.
  // The host will perform write accesses and
  // observe the tags to have been cleared.
  // We do this twice so we can check that both
  // 32-bit and 64-bit writes clear the tags.
  // x8 - Wait for this register to be written before continuing.
  // x9 - UART capability pointer.
  // x10 - Scratch destination register for host issued cgettag instructions.
  // x11, x12, x13, x14 - Clobbers.
  cspecialr     x11, mtdc
  li            x9, TOP_UART0_BASE_ADDR
  csetaddr      x9, x11, x9
  csetboundsimm x9, x9, TOP_UART0_SIZE_BYTES

  li x10, 0
  .irp reg, x1, x2, x3, x4, x5, x6, x7
  cspecialr \reg, mtdc
  .endr

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x9, x11, \ch
  .endr
  wait_here_for_host wait_cheriot_fifth, x8

  li x10, 0
  .irp reg, x1, x2, x3, x4, x5, x6, x7
  cspecialr \reg, mtdc
  .endr

  .irp ch, 'R','E','A','D','Y','\r','\n'
  putc x9, x11, \ch
  .endr
  wait_here_for_host wait_cheriot_sixth, x8

  dv_status t1, t2, DV_STATUS_PASSED
  j .L_park

_fail_ena:
  j _fail_ena
_fail_switch:
  j _trap_handler

.L_park:
  wfi
  j   .L_park


// Trap handler.
  .section .vectors, "ax", @progbits
  .option push
  .option norvc
  .option norelax

  .balign 256
  .globl _trap_handler
_trap_handler:
  csrr t0, misa
  andi t0, t0, MISA_E
  bnez t0, .L_trap_cheriot

  // Trap occured in RV32 mode.
  li t1, TOP_UART0_BASE_ADDR
  li t2, 'R'
  j  .L_trap_print_exit

.L_trap_cheriot:
  // Trap occured in CHERIoT mode.
  cspecialr     ct2, mtdc
  li            t1, TOP_UART0_BASE_ADDR
  csetaddr      ct1, ct2, t1
  csetboundsimm ct1, ct1, TOP_UART0_SIZE_BYTES
  li            t2, 'C'
  j             .L_trap_print_exit

.L_trap_print_exit:
  putr t1, t0, t2
  .irp ch, 'T','R','A','P',' '
  putc t1, t0, \ch
  .endr
  csrr      t2, mcause
  puthex    t1, t0, a0, t2
  .irp ch, '\r', '\n'
  putc      t1, t0, \ch
  .endr
  dv_status t1, t2, DV_STATUS_FAILED
  j .L_park
  .option pop

  .section .rodata, "a", @progbits

  .balign 4
  .globl test_registers
  .type test_registers, @object
test_registers:
  .4byte 0x01234567
  .4byte 0x12345678
  .4byte 0x23456789
  .4byte 0x3456789a
  .4byte 0x456789ab
  .4byte 0x56789abc
  .4byte 0x6789abcd
  .4byte 0x789abcde
  .4byte 0x89abcdef
  .4byte 0x9abcdef0
  .4byte 0xabcdef01
  .4byte 0xbcdef012
  .4byte 0xcdef0123
  .4byte 0xdef01234
  .4byte 0xef012345
  .4byte 0xf0123456
  .size test_registers, . - test_registers

  .balign 8
  .globl test_capabilities
  .type test_capabilities, @object
test_capabilities:
  .8byte 0x0123456789abcdef
  .8byte 0x123456789abcdef0
  .8byte 0x23456789abcdef01
  .8byte 0x3456789abcdef012
  .8byte 0x456789abcdef0123
  .8byte 0x56789abcdef01234
  .8byte 0x6789abcdef012345
  .8byte 0x789abcdef0123456
  .8byte 0x89abcdef01234567
  .8byte 0x9abcdef012345678
  .8byte 0xabcdef0123456789
  .8byte 0xbcdef0123456789a
  .8byte 0xcdef0123456789ab
  .8byte 0xdef0123456789abc
  .8byte 0xef0123456789abcd
  .8byte 0xf0123456789abcde
  .size test_capabilities, . - test_capabilities

.macro value label, v
  .balign 4
  .globl \label
  .type \label, @object
\label:
  .4byte \v
  .size \label, . - \label
.endm

.macro cap label, c
  .balign 8
  .globl \label
  .type \label, @object
\label:
  .8byte \c
  .size \label, . - \label
.endm

  value test_rv32_mscratch, 0xff00ff00
  value test_rv32_mepc, (0xaa55aa55 & ~0b1)
  value test_rv32_mtval, 0xf0f0f0f0

  cap test_cheriot_mscratchc, 0x3737a0a0f2f25151
  cap test_cheriot_mepcc, (0x55aa55aaff00ff00 & ~0b1)
  value test_cheriot_mtval, 0x5555aaaa
