# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Check debug entry at the trap vector after a trap: a step over a denied
# U-mode fetch, a step over a store fault, and an execute trigger on the trap
# vector after a store fault. Each case runs a plain compressed instruction
# first, then a Zcmp one.

#include "riscv_test.h"
#include "test_macros.h"

# dcsr.cause values (ibex_pkg::dbg_cause_e). encoding.h uses older names.
#define DBG_CAUSE_TRIGGER 2
#define DBG_CAUSE_HALTREQ 3
#define DBG_CAUSE_STEP    4

# The bench reads core status at +signature_addr, 4 bytes above SIGNATURE_ADDR.
#define CORE_STATUS_ADDR (SIGNATURE_ADDR + 4)

#define CSR_CPUCTRLSTS      0x7c0
#define CPUCTRLSTS_DUMMY_EN 0x4

# A locked PMP region without permissions denies even M-mode stores to the
# 4KB at 0x90000000, so they never reach the bus. U mode matches no region,
# so it can fetch nothing.
#define PMPADDR0_DENY 0x240001ff
#define PMPCFG0_DENY  0x98
#define STACK_TOP     0x90000800
# cm.push stores the highest register first, at sp - 4.
#define FAULT_ADDR    (STACK_TOP - 4)

# The pinned toolchain has no Zcmp.
# cm.mva01s s0, s7
#define ENC_CM_MVA01S 0xac7e
# cm.push {ra, s0-s11}, -112
#define ENC_CM_PUSH   0xb8fe

# phase (in .data) tracks the progress:
#   0 reset code running
#   1 waiting for the halt request
#   2 stepping over nop_fault in U mode
#   3 stepping over mva_fault in U mode
#   4 stepping over sw_fault
#   5 stepping over push_fault
#   6 running sw_fault with the trigger on trap_vector
#   7 running push_fault with the trigger on trap_vector
#   8 done

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

  # Dummy instructions off, so nothing but the program enters ID.
  li   t0, CPUCTRLSTS_DUMMY_EN
  csrc CSR_CPUCTRLSTS, t0
  csrr t0, CSR_CPUCTRLSTS
  andi t0, t0, CPUCTRLSTS_DUMMY_EN
  bnez t0, fail

  li   t0, PMPADDR0_DENY
  csrw pmpaddr0, t0
  li   t0, PMPCFG0_DENY
  csrw pmpcfg0, t0
  csrr t0, pmpcfg0
  li   t1, PMPCFG0_DENY
  bne  t0, t1, fail

  li   sp, STACK_TOP
  li   a0, FAULT_ADDR

  # Ask for the halt request and wait for it. Its handler resumes at
  # nop_fault, so the loop never sees another phase.
  la   t0, phase
  li   t1, 1
  sw   t1, 0(t0)
  li   t0, CORE_STATUS_ADDR
  li   t1, (INITIALIZED << 8) | CORE_STATUS
  sw   t1, 0(t0)
  li   t2, 100000
1:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  bne  t0, t1, fail
  addi t2, t2, -1
  bnez t2, 1b
  j    fail

  # Reached only from debug mode. Every instruction traps, so no jump to fail
  # is executed. The first two run in U mode, where both fetches fault.
  .balign 4
nop_fault:
  c.nop
  j    fail
mva_fault:
  .2byte ENC_CM_MVA01S
  j    fail

  .balign 4
sw_fault:
  c.sw a1, 0(a0)
  j    fail
push_fault:
  .2byte ENC_CM_PUSH
  j    fail

done:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 8
  bne  t0, t1, fail
  j    pass

  TEST_PASSFAIL

  # Each step or trigger enters debug mode before the first instruction of the
  # trap handler, and the debug handler moves on.
mtvec_handler:
  j    fail

# Checks an entry with \cause at the trap vector after \insn trapped with
# \mcause. The trap handler runs in M mode.
.macro check_trap_entry cause, insn, mcause
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, \cause
  bne  t0, t1, fail
  csrr t0, dcsr
  andi t0, t0, DCSR_PRV
  li   t1, PRV_M
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, trap_vector
  bne  t0, t1, fail
  csrr t0, mcause
  li   t1, \mcause
  bne  t0, t1, fail
  csrr t0, mepc
  la   t1, \insn
  bne  t0, t1, fail
.endm

# Checks an entry with \cause after the fetch of \insn faulted.
.macro check_fetch_fault cause, insn
  check_trap_entry \cause, \insn, CAUSE_FETCH_ACCESS
  csrr t0, mtval
  la   t1, \insn
  bne  t0, t1, fail
.endm

# Checks an entry with \cause after \insn faulted on FAULT_ADDR.
.macro check_store_fault cause, insn
  check_trap_entry \cause, \insn, CAUSE_STORE_ACCESS
  csrr t0, mtval
  li   t1, FAULT_ADDR
  bne  t0, t1, fail
.endm

debug_entry:
  csrw dscratch0, t0
  csrw dscratch1, t1
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  beq  t0, t1, debug_halt
  li   t1, 2
  beq  t0, t1, debug_step_nop
  li   t1, 3
  beq  t0, t1, debug_step_mva
  li   t1, 4
  beq  t0, t1, debug_step_sw
  li   t1, 5
  beq  t0, t1, debug_step_push
  li   t1, 6
  beq  t0, t1, debug_trigger_sw
  li   t1, 7
  beq  t0, t1, debug_trigger_push
  j    fail

debug_halt:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_HALTREQ
  bne  t0, t1, fail
  # Step in U mode (dcsr.prv = PRV_U = 0).
  li   t0, DCSR_STEP
  csrs dcsr, t0
  li   t0, DCSR_PRV
  csrc dcsr, t0
  la   t0, nop_fault
  csrw dpc, t0
  li   t0, 2
  j    debug_set_phase

debug_step_nop:
  check_fetch_fault DBG_CAUSE_STEP, nop_fault
  li   t0, DCSR_PRV
  csrc dcsr, t0
  la   t0, mva_fault
  csrw dpc, t0
  li   t0, 3
  j    debug_set_phase

debug_step_mva:
  check_fetch_fault DBG_CAUSE_STEP, mva_fault
  # Step the store faults in M mode, which dcsr.prv now holds.
  la   t0, sw_fault
  csrw dpc, t0
  li   t0, 4
  j    debug_set_phase

debug_step_sw:
  check_store_fault DBG_CAUSE_STEP, sw_fault
  la   t0, push_fault
  csrw dpc, t0
  li   t0, 5
  j    debug_set_phase

debug_step_push:
  check_store_fault DBG_CAUSE_STEP, push_fault
  # Nothing of the sequence retired, so sp has not moved.
  li   t1, STACK_TOP
  bne  sp, t1, fail
  # Stop stepping and set an execute trigger on trap_vector (write tdata1
  # last, as the debug spec says).
  li   t0, DCSR_STEP
  csrc dcsr, t0
  csrwi tselect, 0
  csrw tdata1, zero
  la   t0, trap_vector
  csrw tdata2, t0
  csrwi tdata1, 5
  la   t0, sw_fault
  csrw dpc, t0
  li   t0, 6
  j    debug_set_phase

debug_trigger_sw:
  check_store_fault DBG_CAUSE_TRIGGER, sw_fault
  # Keep the trigger.
  la   t0, push_fault
  csrw dpc, t0
  li   t0, 7
  j    debug_set_phase

debug_trigger_push:
  check_store_fault DBG_CAUSE_TRIGGER, push_fault
  csrw tdata1, zero
  la   t0, done
  csrw dpc, t0
  li   t0, 8

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
