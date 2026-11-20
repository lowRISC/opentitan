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
 * The switch to CHERIoT follows the runtime switch sequence in the rv_core_ibex
 * documentation.
 *
 * Emits a marker straight to UART0 and parks the core. Whatever booted it has
 * already configured UART0 for its own logging, so no driver setup is needed.
 */

#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/multibits_asm.h"
#include "hw/top/rv_core_ibex_regs.h"  // Generated.
#include "hw/top/sram_ctrl_regs.h"  // Generated.
#include "hw/top/top_memory.h" // Generated.
#include "hw/top/uart_regs.h"  // Generated.

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

#define MSTATUS_MIE (1 << 3)
#define CPUCTRL_DUMMY_INSTR_EN (1 << 2)

// Bounds the wait for CHERIoT mode, far above the switch latency.
#define SWITCH_POLL_LIMIT 0x1000

#define SRAM_CTRL_STATUS_ERRORS                                            \
  ((1 << SRAM_CTRL_STATUS_BUS_INTEG_ERROR_BIT) |                           \
   (1 << SRAM_CTRL_STATUS_INIT_ERROR_BIT) |                                \
   (1 << SRAM_CTRL_STATUS_ESCALATED_BIT) |                                 \
   (1 << SRAM_CTRL_STATUS_READBACK_ERROR_BIT) |                            \
   (1 << SRAM_CTRL_STATUS_SRAM_ALERT_BIT))

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
 * Trap handler. Every trap is fatal: it raises the fatal software alert, then
 * emits one of
 *
 *   RTRAP <mcause>    entered in RV32 mode - the mode switch did not take
 *   CTRAP <mcause>    entered in CHERIoT mode - the switch worked, something
 *                     after it faulted
 *
 * telling the two apart by MISA.E.
 *
 * `mtvec` is set before the switch, while a plain `csrw` to it is still legal.
 * RV32 mode vectors (exceptions at the base, NMIs at base + 0x7C). Until `mtcc`
 * is set up after the switch, CHERIoT mode enters every trap at the `mtvec`
 * base, so the body checks the mode. `mtcc` then points at the CHERIoT part.
 *
 * NMIs cannot be masked, so the mode can also change while the RV32 path runs.
 * Its stores then fault before any bus access and the trap re-enters in
 * CHERIoT mode. Raising the alert twice is harmless.
 *
 * Only the base register setup differs between the two paths; the shared body
 * must stick to instructions that encode identically in both modes, which
 * rules out advancing a pointer through the string.
 */
  .section .vectors, "ax", @progbits
  .option push
  .option norvc
  .option norelax

  // The RV32 vector table base must be 256-byte aligned.
  .balign 256
  .globl _trap_handler
  .type _trap_handler, @function
_trap_handler:
  .rept 32
  j    .L_trap_body
  .endr

.L_trap_body:
  csrr t0, misa
  andi t0, t0, MISA_E
  bnez t0, _trap_handler_cheriot

  // RV32: an integer base is all the stores need.
  lui  t1, %hi(TOP_RV_CORE_IBEX_CFG_BASE_ADDR)
  li   t2, MULTIBIT_ASM_BOOL4_TRUE
  sw   t2, RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET(t1)
  lui  t1, %hi(TOP_UART0_BASE_ADDR)
  addi t2, x0, 'R'
  j    .L_trap_mark

  .balign 4
_trap_handler_cheriot:
  // CHERIoT: the stores need capabilities. `mtdc` is still the memory root, so
  // derive them from it.
  cspecialr t1, mtdc
  lui       t2, %hi(TOP_RV_CORE_IBEX_CFG_BASE_ADDR)
  csetaddr  t2, t1, t2
  li        a0, MULTIBIT_ASM_BOOL4_TRUE
  sw        a0, RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET(t2)
  lui       t2, %hi(TOP_UART0_BASE_ADDR)
  csetaddr  t1, t1, t2
  csetboundsimm t1, t1, TOP_UART0_SIZE_BYTES
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
  li s0, TOP_UART0_BASE_ADDR
  li s1, TOP_RV_CORE_IBEX_CFG_BASE_ADDR

  // Install the diagnostic trap handler first, so that it is already armed if
  // the switch itself faults.
  lui  t0, %hi(_trap_handler)
  addi t0, t0, %lo(_trap_handler)
  csrw mtvec, t0

  // No interrupts until the end. The handler above takes NMIs in either mode.
  csrci mstatus, MSTATUS_MIE
  csrw  mie, x0

#if CHERIOT_MODE
  // Zero the capability tags and the revocation bitmap. Nothing before this
  // stage initializes the meta SRAM.
  li   a0, TOP_SRAM_CTRL_META_REGS_BASE_ADDR
  li   t0, (1 << SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT) | \
           (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw   t0, SRAM_CTRL_CTRL_REG_OFFSET(a0)
.L_meta_init_wait:
  lw   t0, SRAM_CTRL_STATUS_REG_OFFSET(a0)
  andi t1, t0, SRAM_CTRL_STATUS_ERRORS
  bnez t1, _fail_meta_init
  andi t1, t0, (1 << SRAM_CTRL_STATUS_INIT_DONE_BIT)
  beqz t1, .L_meta_init_wait

  // Lock re-keying of the meta SRAM and the tagged SRAMs. In CHERIoT mode it
  // would leave stale tags on the new contents. This is not required: if
  // re-keying must stay possible, e.g. to wipe the SRAMs on shutdown, only hand
  // capabilities to these registers to trusted code instead.
  sw   x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(a0)
  li   t0, TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  sw   x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(t0)
  li   t0, TOP_SRAM_CTRL_SEC_REGS_BASE_ADDR
  sw   x0, SRAM_CTRL_CTRL_REGWEN_REG_OFFSET(t0)

  // x16-x31 hold the capability metadata of x0-x15 in CHERIoT mode, so zero
  // them, and keep dummy instructions off until the core is in CHERIoT mode.
  csrr  a1, CSR_REG_CPUCTRL
  csrci CSR_REG_CPUCTRL, CPUCTRL_DUMMY_INSTR_EN
  .option push
  .option arch, rv32i_zicsr
  .irp reg, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31
  li   \reg, 0
  .endr
  .option pop
#endif

  // Select the mode. The switch FSM accepts only the strict MuBi4 encodings of
  // `CHERIOT_ENA`; on anything else the `CHERIOT_LOCK` write parks it in a
  // terminal error state, where CHERIoT mode stays unavailable until reset and
  // the fatal alert is raised. Read `CHERIOT_ENA` back first so a value that
  // did not land fails the test here rather than taking the chip down.
  addi t0, x0, ENA_SELECTED
  sw   t0, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  lw   t1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(s1)
  bne  t0, t1, _fail_ena

#if CHERIOT_MODE
  li   a3, SWITCH_POLL_LIMIT
#endif

  // Commit. `CHERIOT_ENA` is only sampled here, and this write is once-only.
  addi t0, x0, MULTIBIT_ASM_BOOL4_TRUE
  sw   t0, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(s1)
  fence.i

#if CHERIOT_MODE
  // The mode changes some cycles after the write. Until it does, only use
  // instructions that behave the same in both modes. `misa.E` marks CHERIoT
  // mode only because ePMP mode runs RV32I on Earl Grey.
.L_switch_wait:
  csrr t2, misa
  andi t2, t2, MISA_E
  bnez t2, .L_switched
  addi a3, a3, -1
  bnez a3, .L_switch_wait
  beq  x0, x0, _fail_switch
.L_switched:
  csrw CSR_REG_CPUCTRL, a1

  // Set up `mtcc` before anything that can trap.
  cllc      ct0, _trap_handler_cheriot
  cspecialw mtcc, ct0
#endif
  .option pop

  // This concludes the switch. The rest of the test checks that it worked.

#if CHERIOT_MODE
  // No register may hold a tagged capability, except t0, which now holds the
  // `mtcc` capability. Reading them also checks their metadata ECC, as an error
  // halts the core.
  cgettag a4, a4
  cgettag t2, t2
  or      a4, a4, t2
  .irp reg, ra, sp, gp, tp, t1, s0, s1, a0, a1, a2, a3, a5
  cgettag t2, \reg
  or      a4, a4, t2
  .endr

  // MMIO now needs capabilities. `mtdc` still holds the memory root: nothing
  // in the RV32 boot stages writes it.
  cspecialr ct1, mtdc
  li        t2, TOP_UART0_BASE_ADDR
  csetaddr  cs0, ct1, t2
  csetboundsimm cs0, cs0, TOP_UART0_SIZE_BYTES
  li        t2, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  csetaddr  cs1, ct1, t2
  csetboundsimm cs1, cs1, TOP_RV_CORE_IBEX_CFG_SIZE_BYTES

  // Only report now: the failure reporter needs the capabilities in s0 and s1.
  bnez a4, _fail_reg_tag

  // The tag memory is clear, at both ends of main SRAM and in the NVM.
  li       t2, TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR
  csetaddr ca2, ct1, t2
  csetboundsimm ca2, ca2, 8
  clc      ca3, 0(ca2)
  cgettag  t2, ca3
  bnez     t2, _fail_tag
  li       t2, (TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR + \
                TOP_SRAM_CTRL_MAIN_RAM_SIZE_BYTES - 8)
  csetaddr ca3, ct1, t2
  clc      ca3, 0(ca3)
  cgettag  t2, ca3
  bnez     t2, _fail_tag
  cllc     ca3, kPassMsg
  cgetaddr t2, ca3
  andi     t2, t2, -8
  csetaddr ca3, ct1, t2
  clc      ca3, 0(ca3)
  cgettag  t2, ca3
  bnez     t2, _fail_tag

  // And a stored capability loads back unchanged, tag included.
  csc      ca2, 0(ca2)
  clc      ca3, 0(ca2)
  csetequalexact t2, ca3, ca2
  beqz     t2, _fail_tag_store

  // A main SRAM re-key would stall the reload below until done and change what
  // it reads.
  li       t2, TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR
  csetaddr ca4, ct1, t2
  csetboundsimm ca4, ca4, TOP_SRAM_CTRL_MAIN_REGS_SIZE_BYTES
  li       t0, (1 << SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT) | \
               (1 << SRAM_CTRL_CTRL_INIT_BIT)
  csw      t0, SRAM_CTRL_CTRL_REG_OFFSET(ca4)
  clc      ca4, 0(ca2)
  csetequalexact t2, ca4, ca2
  beqz     t2, _fail_sram_ctrl_lock
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
 *   I    the meta SRAM initialization reported an error
 *   W    the core did not reach CHERIoT mode after the `CHERIOT_LOCK` write
 *   G    a register held a tagged capability right after the switch
 *   T    the tag memory was not clear after its initialization
 *   C    a stored capability did not load back unchanged
 *   K    a main SRAM key renewal changed a stored capability after the lock
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
_fail_meta_init:
  addi a0, x0, 'I'
  j    _fail
_fail_switch:
  addi a0, x0, 'W'
  j    _fail
_fail_reg_tag:
  addi a0, x0, 'G'
  j    _fail
_fail_tag:
  addi a0, x0, 'T'
  j    _fail
_fail_tag_store:
  addi a0, x0, 'C'
  j    _fail
_fail_sram_ctrl_lock:
  addi a0, x0, 'K'
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
