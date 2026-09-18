// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Checks that the ePMP/CHERIoT execution mode switch selects and locks a mode.
 *
 * `CHERIOT_MODE` picks which mode the image boots into: 1 switches to CHERIoT,
 * 0 stays in ePMP. Both paths lock the mode and then confirm that the choice
 * cannot be revoked, so between them they cover both locked states of the
 * switch FSM.
 *
 * Emits a marker straight to UART0 and parks the core. Whatever booted it has
 * already configured UART0 for its own logging, so no driver setup is needed.
 */

#include "sw/device/lib/base/multibits_asm.h"
#include "hw/top/rv_core_ibex_regs.h"  // Generated.
#include "hw/top/uart_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"

#if !defined(CHERIOT_MODE)
#error "CHERIOT_MODE must be 1 (boot into CHERIoT) or 0 (stay in ePMP)."
#endif

// Test status values for the DV window. A pass is only accepted directly from
// `IN_TEST`. Compiled in for DV alone: a write to the window ends a Verilator
// run, cutting the console marker short.
#define DV_STATUS_IN_TEST 0x4354
#define DV_STATUS_PASSED 0x900d
#define DV_STATUS_FAILED 0xbaad

// MISA.E reads as set only while CHERIoT mode is active, and MISA.I is driven
// as its complement; only two of the four bit patterns are valid. Checking
// either bit alone would admit one of the invalid ones.
#define MISA_E (1 << 4)
#define MISA_I (1 << 8)
#define MISA_MODE (MISA_E | MISA_I)

#if CHERIOT_MODE
#define ENA_SELECTED MULTIBIT_ASM_BOOL4_TRUE
#define ENA_REJECTED MULTIBIT_ASM_BOOL4_FALSE
#define MISA_MODE_EXPECTED MISA_E
#define PASS_MSG "CHERIoT PASS!\r\n"
#else
#define ENA_SELECTED MULTIBIT_ASM_BOOL4_FALSE
#define ENA_REJECTED MULTIBIT_ASM_BOOL4_TRUE
#define MISA_MODE_EXPECTED MISA_I
#define PASS_MSG "ePMP PASS!\r\n"
#endif

// -----------------------------------------------------------------------------

/**
 * Trap handler, for diagnostics only.
 *
 * Without this a failure is just silence on the console. This emits one of
 *
 *   RTRAP <mcause>    entered in RV32 mode - the mode switch did not take
 *   CTRAP <mcause>    entered in CHERIoT mode - the switch worked, something
 *                     after it faulted
 *
 * telling the two apart by MISA.E.
 *
 * `mtvec` is installed in direct mode before the mode switch, while a plain
 * `csrw` to it is still legal, so no vector table is needed. It stays valid
 * afterwards: an RV32-mode write only updates the address half, leaving
 * `mtvec_cap` at the executable root, so in CHERIoT mode `mtcc` still points
 * here with a PCC that covers it.
 *
 * Only the base register setup differs between the two paths; the shared body
 * must stick to instructions that encode identically in both modes, which
 * rules out advancing a pointer through the string.
 */
  .section .vectors, "ax", @progbits
  .option push
  .option norvc
  .option norelax

  // mtvec direct mode requires the address to be 4-byte aligned; the 256-byte
  // alignment is the Ibex convention for this section.
  .balign 256
  .globl _trap_handler
  .type _trap_handler, @function
_trap_handler:
  csrr t0, misa
  andi t0, t0, MISA_E
  bnez t0, .L_trap_cheriot

  // RV32: an integer base is all the store needs.
  lui  t1, %hi(TOP_EARLGREY_UART0_BASE_ADDR)
  addi t2, x0, 'R'
  j    .L_trap_mark

.L_trap_cheriot:
  // CHERIoT: the store needs a capability. `mtdc` is still the memory root, so
  // narrow a copy of it onto the UART register window.
  cspecialr t1, mtdc
  lui       t2, %hi(TOP_EARLGREY_UART0_BASE_ADDR)
  csetaddr  t1, t1, t2
  csetboundsimm t1, t1, 0x40
  addi      t2, x0, 'C'

.L_trap_mark:
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'T'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'R'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'A'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'P'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, ' '
  sw   t2, UART_WDATA_REG_OFFSET(t1)

  // `mcause` as eight hex digits, most significant first.
  csrr s0, mcause
  addi s1, x0, 8
.L_trap_nibble:
  srli a0, s0, 28
  slli s0, s0, 4
  addi a1, x0, 10
  blt  a0, a1, .L_trap_digit
  addi a0, a0, ('a' - 10 - '0')
.L_trap_digit:
  addi a0, a0, '0'
  sw   a0, UART_WDATA_REG_OFFSET(t1)
  addi s1, s1, -1
  bnez s1, .L_trap_nibble

  addi t2, x0, '\r'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, '\n'
  sw   t2, UART_WDATA_REG_OFFSET(t1)

.L_trap_park:
  wfi
  j    .L_trap_park
  .size _trap_handler, . - _trap_handler

  .option pop

// -----------------------------------------------------------------------------

  .section .crt, "ax", @progbits
  .balign 4
  .globl _ottf_start
  .type _ottf_start, @function
_ottf_start:
  // Whatever booted this hands over with the core still in RV32 mode, so
  // everything up to the switch below executes as RV32 despite being assembled
  // for CHERIoT. That works because CHERIoT reuses the standard load/store
  // encodings, so `sw t1, off(t0)` and `csw t1, off(ct0)` are the same four
  // bytes; expect the disassembly to show the stores as `ct.csw`.
  //
  // Compression and relaxation are off so the encodings cannot depend on
  // assembler choices.
  .option push
  .option norvc
  .option norelax

  // Integer MMIO bases. They stay valid for as long as the core is in RV32
  // mode; a CHERIoT build re-derives them as capabilities after the switch.
  li s0, TOP_EARLGREY_UART0_BASE_ADDR
  li s1, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR

  // Install the diagnostic trap handler first, in direct mode, so that it is
  // already armed if the switch itself faults.
  lui  t0, %hi(_trap_handler)
  addi t0, t0, %lo(_trap_handler)
  csrw mtvec, t0

  // Select the mode. The switch FSM accepts only the strict MuBi4 encodings of
  // `CHERIOT_ENA`; on anything else the `CHERIOT_LOCK` write parks it in a
  // terminal error state, where CHERIoT mode stays unavailable until reset and
  // the fatal alert is raised. Read `CHERIOT_ENA` back first so a value that
  // did not land fails the test here rather than taking the chip down.
  addi t0, x0, ENA_SELECTED
  sw   t0, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  lw   t1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  bne  t0, t1, _fail_ena

  // Commit. `CHERIOT_ENA` is only sampled here, and this write is once-only.
  addi t0, x0, MULTIBIT_ASM_BOOL4_TRUE
  sw   t0, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(s1)
  fence.i
  .option pop

#if CHERIOT_MODE
  // MMIO now needs capabilities. `mtdc` still holds the memory root: nothing
  // in the RV32 boot stages writes it.
  cspecialr ct1, mtdc
  li        t2, TOP_EARLGREY_UART0_BASE_ADDR
  csetaddr  cs0, ct1, t2
  csetboundsimm cs0, cs0, 0x40
  li        t2, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR
  csetaddr  cs1, ct1, t2
  csetboundsimm cs1, cs1, 0xa0
#endif

  // Confirm the core really is in the mode that was asked for.
  csrr t0, misa
  andi t0, t0, MISA_MODE
  addi t1, x0, MISA_MODE_EXPECTED
  bne  t0, t1, _fail_mode

#ifdef DV_TEST_STATUS
  li   t0, DV_STATUS_IN_TEST
  sw   t0, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(s1)
#endif

  // The mode is locked, but `CHERIOT_ENA` stays writable: the FSM samples it
  // only on the first `CHERIOT_LOCK` write. Ask for the other mode, write
  // `CHERIOT_LOCK` again, and check the core did not follow. The read-back
  // stops the check being vacuous: if the write never landed, an unchanged
  // mode would prove nothing.
  addi t0, x0, ENA_REJECTED
  sw   t0, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  lw   t1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  bne  t0, t1, _fail_ena_stuck

  addi t0, x0, MULTIBIT_ASM_BOOL4_TRUE
  sw   t0, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(s1)
  fence.i

  csrr t0, misa
  andi t0, t0, MISA_MODE
  addi t1, x0, MISA_MODE_EXPECTED
  bne  t0, t1, _fail_lock

  // Walk the null-terminated marker string.
#if CHERIOT_MODE
  cllc     ca2, kPassMsg
#else
  lui      a2, %hi(kPassMsg)
  addi     a2, a2, %lo(kPassMsg)
#endif

.L_tx_next:
  lbu      a4, 0(a2)
  beqz     a4, .L_done
#if CHERIOT_MODE
  cincoffsetimm ca2, ca2, 1
#else
  addi     a2, a2, 1
#endif

  // Spin while the transmit FIFO is full, then push the byte.
.L_tx_wait:
  lw       a5, UART_STATUS_REG_OFFSET(s0)
  andi     a5, a5, (1 << UART_STATUS_TXFULL_BIT)
  bnez     a5, .L_tx_wait
  sw       a4, UART_WDATA_REG_OFFSET(s0)
  j        .L_tx_next

.L_done:
#ifdef DV_TEST_STATUS
  li   t0, DV_STATUS_PASSED
  sw   t0, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(s1)
#endif
.L_park:
  wfi
  j        .L_park
  .size _ottf_start, . - _ottf_start

// -----------------------------------------------------------------------------

/**
 * Failure reporter, reached from either side of the mode switch.
 *
 * Emits `FAIL <letter>`, where the letter names the check that failed:
 *
 *   E    `CHERIOT_ENA` did not read back as written, before locking
 *   M    the core came out of the switch in the wrong mode
 *   S    `CHERIOT_ENA` did not read back as written, after locking, so the
 *        revocation attempt below it would not have proved anything
 *   L    the mode followed a post-lock `CHERIOT_ENA` change
 *
 * `s0` holds an integer address before the switch and a capability after it,
 * and the stores here encode identically either way, so one reporter serves
 * both.
 */
  .balign 4
_fail_ena:
  addi a0, x0, 'E'
  j    _fail
_fail_mode:
  addi a0, x0, 'M'
  j    _fail
_fail_ena_stuck:
  addi a0, x0, 'S'
  j    _fail
_fail_lock:
  addi a0, x0, 'L'
  j    _fail

  .type _fail, @function
_fail:
  addi t2, x0, 'F'
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, 'A'
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, 'I'
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, 'L'
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, ' '
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  sw   a0, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, '\r'
  sw   t2, UART_WDATA_REG_OFFSET(s0)
  addi t2, x0, '\n'
  sw   t2, UART_WDATA_REG_OFFSET(s0)

#ifdef DV_TEST_STATUS
  li   t0, DV_STATUS_FAILED
  sw   t0, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(s1)
#endif
.L_fail_park:
  wfi
  j    .L_fail_park
  .size _fail, . - _fail

  .section .rodata, "a", @progbits
  .balign 4
kPassMsg:
  .asciz PASS_MSG
