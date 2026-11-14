# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# An ebreak, a single step or a halt request enters debug mode while an
# execute trigger is set on the next address: dcsr.cause must name that entry,
# not the trigger. Between the cases, checks that the trigger fires on an
# address the program reaches, also as the first instruction of a step and
# after the halt. The bench sends a halt request each time the core sleeps in
# WFI.

#include "riscv_test.h"
#include "test_macros.h"

# dcsr.cause values (ibex_pkg::dbg_cause_e). encoding.h uses older names.
#define DBG_CAUSE_EBREAK  1
#define DBG_CAUSE_TRIGGER 2
#define DBG_CAUSE_HALTREQ 3
#define DBG_CAUSE_STEP    4

# phase (in .data) tracks the progress:
#   0 reset code running
#   1 halt request from WFI, no trigger set
#   2 running to the trigger on hit
#   3 running the ebreak, trigger after it
#   4 stepping over step_16, trigger after it
#   5 stepping onto the trigger on hit
#   6 stepping over illegal_32, trigger after it
#   7 halt request from WFI, trigger after the WFI
#   8 resuming onto that trigger
#   9 done

# DmHaltAddr is the start of .text.init and DmExceptionAddr 8 bytes later. The
# reset code of RVTEST_CODE_BEGIN starts at offset 0x80.
  .section .text.init
  .option push
  .option norvc
  j    debug_entry
  nop
  j    fail
  .option pop

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Wait for the first halt request. Its handler resumes at before_hit.
  la   t0, phase
  li   t1, 1
  sw   t1, 0(t0)
  wfi
after_first_wfi:
  j    fail

  # Reached only from debug mode. Each case stops the program before the
  # jump to fail that follows it.
  .balign 4
  .option push
  .option norvc
before_hit:
  nop
hit:
  j    fail
ebreak_32:
  ebreak
after_ebreak:
  j    fail
illegal_32:
  # csrrw zero, cycle, zero: cycle is read-only, so this is illegal.
  .word 0xc0001073
after_illegal:
  j    fail
wfi_32:
  wfi
after_wfi:
  j    fail
  .option pop
step_16:
  c.nop
after_step:
  j    fail

done:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 9
  bne  t0, t1, fail
  j    pass

  TEST_PASSFAIL

  # Only the step over illegal_32 traps, and it enters debug mode before the
  # first instruction of this handler. An ebreak that did not enter debug mode
  # ends here.
mtvec_handler:
  j    fail

# Fails unless dcsr.cause is \cause and dpc is \addr.
.macro check_entry cause, addr
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, \cause
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, \addr
  bne  t0, t1, fail
.endm

# Sets the execute trigger on \addr (tdata1 last, as the debug spec says).
.macro set_trigger addr
  csrw tdata1, zero
  la   t0, \addr
  csrw tdata2, t0
  csrwi tdata1, 5
.endm

debug_entry:
  csrw dscratch0, t0
  csrw dscratch1, t1
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  beq  t0, t1, debug_halt
  li   t1, 2
  beq  t0, t1, debug_hit
  li   t1, 3
  beq  t0, t1, debug_ebreak
  li   t1, 4
  beq  t0, t1, debug_step
  li   t1, 5
  beq  t0, t1, debug_step_hit
  li   t1, 6
  beq  t0, t1, debug_step_trap
  li   t1, 7
  beq  t0, t1, debug_wfi_halt
  li   t1, 8
  beq  t0, t1, debug_wfi_hit
  j    fail

debug_halt:
  check_entry DBG_CAUSE_HALTREQ, after_first_wfi
  csrwi tselect, 0
  set_trigger hit
  la   t0, before_hit
  csrw dpc, t0
  li   t0, 2
  j    debug_set_phase

debug_hit:
  check_entry DBG_CAUSE_TRIGGER, hit
  set_trigger after_ebreak
  li   t0, DCSR_EBREAKM
  csrs dcsr, t0
  la   t0, ebreak_32
  csrw dpc, t0
  li   t0, 3
  j    debug_set_phase

debug_ebreak:
  check_entry DBG_CAUSE_EBREAK, ebreak_32
  li   t0, DCSR_EBREAKM
  csrc dcsr, t0
  set_trigger after_step
  li   t0, DCSR_STEP
  csrs dcsr, t0
  la   t0, step_16
  csrw dpc, t0
  li   t0, 4
  j    debug_set_phase

debug_step:
  check_entry DBG_CAUSE_STEP, after_step
  # Keep stepping, but resume onto a trigger: it fires before hit executes.
  set_trigger hit
  la   t0, hit
  csrw dpc, t0
  li   t0, 5
  j    debug_set_phase

debug_step_hit:
  check_entry DBG_CAUSE_TRIGGER, hit
  set_trigger after_illegal
  la   t0, illegal_32
  csrw dpc, t0
  li   t0, 6
  j    debug_set_phase

debug_step_trap:
  check_entry DBG_CAUSE_STEP, trap_vector
  csrr t0, mcause
  li   t1, CAUSE_ILLEGAL_INSTRUCTION
  bne  t0, t1, fail
  li   t0, DCSR_STEP
  csrc dcsr, t0
  set_trigger after_wfi
  la   t0, wfi_32
  csrw dpc, t0
  li   t0, 7
  j    debug_set_phase

debug_wfi_halt:
  # Resume at dpc with the trigger still set: it fires before after_wfi
  # executes.
  check_entry DBG_CAUSE_HALTREQ, after_wfi
  li   t0, 8
  j    debug_set_phase

debug_wfi_hit:
  check_entry DBG_CAUSE_TRIGGER, after_wfi
  csrw tdata1, zero
  la   t0, done
  csrw dpc, t0
  li   t0, 9

debug_set_phase:
  la   t1, phase
  sw   t0, 0(t1)

debug_resume:
  csrr t0, dscratch0
  csrr t1, dscratch1
  dret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
phase:
  .word 0
RVTEST_DATA_END
