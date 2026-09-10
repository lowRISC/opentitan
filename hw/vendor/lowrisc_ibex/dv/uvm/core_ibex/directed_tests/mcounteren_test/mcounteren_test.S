# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This test verifies mcounteren CSR functionality by sweeping multiple bit
# patterns to ensure User-mode access to all 64 performance counters is
# correctly gated. It confirms that allowed registers read successfully,
# while disabled registers securely trigger illegal instruction exceptions.

#include "custom_macros.h"
#include "riscv_test.h"
#include "test_macros.h"

# Register Allocation:
# s0: mcounteren WARL readback used by check_counter_aliases
# s1: Expected instruction execution state(1 = should succeed, 0 = should trap)
# s2: Readback snapshot of valid mcounteren bits
# s3: Subroutine return address backup tracking register(ra)
# s4: Label pointing to the next macro boundary
# s5: Subroutine continuation target pointer used upon full block completion

.macro RUN_CSR_TEST idx, csr_addr
  # Check if this counter is configured to be accessible
  # Get position at which to check mcounteren bit for this counter
  li    t0, \csr_addr
  andi  t0, t0, 0x1F
  # Create mask from position
  li    t1, 1
  sll   t1, t1, t0
  and   t1, s2, t1
  # s1 = 1 if counter is enabled and should succeed cleanly
  snez  s1, t1

  # Set next test label for the handler
  la    s4, next_test_\idx

  # Read counter.This should trap if s1 == 0 and succeed if s1 == 1
  csrr  t0, \csr_addr
  # If the counter was supposed to trap but didn't, fail immediately
  beqz  s1, fail
  # Continue to next test
next_test_\idx:
.endm

.macro RUN_ALL_CSR_TESTS
  # Lower 32 Bits of Performance Counters
  RUN_CSR_TEST  0, 0xC00   # cycle
  RUN_CSR_TEST  1, 0xC01   # time
  RUN_CSR_TEST  2, 0xC02   # instret
  RUN_CSR_TEST  3, 0xC03   # hpmcounter3
  RUN_CSR_TEST  4, 0xC04
  RUN_CSR_TEST  5, 0xC05
  RUN_CSR_TEST  6, 0xC06
  RUN_CSR_TEST  7, 0xC07
  RUN_CSR_TEST  8, 0xC08
  RUN_CSR_TEST  9, 0xC09
  RUN_CSR_TEST 10, 0xC0A
  RUN_CSR_TEST 11, 0xC0B
  RUN_CSR_TEST 12, 0xC0C
  RUN_CSR_TEST 13, 0xC0D
  RUN_CSR_TEST 14, 0xC0E
  RUN_CSR_TEST 15, 0xC0F
  RUN_CSR_TEST 16, 0xC10
  RUN_CSR_TEST 17, 0xC11
  RUN_CSR_TEST 18, 0xC12
  RUN_CSR_TEST 19, 0xC13
  RUN_CSR_TEST 20, 0xC14
  RUN_CSR_TEST 21, 0xC15
  RUN_CSR_TEST 22, 0xC16
  RUN_CSR_TEST 23, 0xC17
  RUN_CSR_TEST 24, 0xC18
  RUN_CSR_TEST 25, 0xC19
  RUN_CSR_TEST 26, 0xC1A
  RUN_CSR_TEST 27, 0xC1B
  RUN_CSR_TEST 28, 0xC1C
  RUN_CSR_TEST 29, 0xC1D
  RUN_CSR_TEST 30, 0xC1E
  RUN_CSR_TEST 31, 0xC1F   # hpmcounter31
  # Upper 32 Bits of Performance Counters
  RUN_CSR_TEST 32, 0xC80   # cycleh
  RUN_CSR_TEST 33, 0xC81   # timeh
  RUN_CSR_TEST 34, 0xC82   # instreth
  RUN_CSR_TEST 35, 0xC83   # hpmcounter3h
  RUN_CSR_TEST 36, 0xC84
  RUN_CSR_TEST 37, 0xC85
  RUN_CSR_TEST 38, 0xC86
  RUN_CSR_TEST 39, 0xC87
  RUN_CSR_TEST 40, 0xC88
  RUN_CSR_TEST 41, 0xC89
  RUN_CSR_TEST 42, 0xC8A
  RUN_CSR_TEST 43, 0xC8B
  RUN_CSR_TEST 44, 0xC8C
  RUN_CSR_TEST 45, 0xC8D
  RUN_CSR_TEST 46, 0xC8E
  RUN_CSR_TEST 47, 0xC8F
  RUN_CSR_TEST 48, 0xC90
  RUN_CSR_TEST 49, 0xC91
  RUN_CSR_TEST 50, 0xC92
  RUN_CSR_TEST 51, 0xC93
  RUN_CSR_TEST 52, 0xC94
  RUN_CSR_TEST 53, 0xC95
  RUN_CSR_TEST 54, 0xC96
  RUN_CSR_TEST 55, 0xC97
  RUN_CSR_TEST 56, 0xC98
  RUN_CSR_TEST 57, 0xC99
  RUN_CSR_TEST 58, 0xC9A
  RUN_CSR_TEST 59, 0xC9B
  RUN_CSR_TEST 60, 0xC9C
  RUN_CSR_TEST 61, 0xC9D
  RUN_CSR_TEST 62, 0xC9E
  RUN_CSR_TEST 63, 0xC9F   # hpmcounter31h
.endm

# Freeze one HPM counter, write it, drop to U-mode to read the user-mode alias,
# then verify the values match.
# s0 is the mcounteren readback on entry
# s1 carries the M-mode read.
# s2 carries the U-mode read.
.macro CHECK_HPM_ALIAS_ONE idx, mhpmcsr, hpmcsr
  li    t0, (1 << \idx)
  and   t1, t0, s0
  beqz  t1, skip_hpm_alias_\hpmcsr

  csrs  mcountinhibit, t0
  li    t0, (0x12345678 ^ \idx)
  csrw  \mhpmcsr, t0
  csrr  s1, \mhpmcsr

  la    s5, after_hpm_alias_\hpmcsr
  SWITCH_TO_U_MODE_LABEL(hpm_alias_u_\hpmcsr)

.balign 4
hpm_alias_u_\hpmcsr:
  csrr  s2, \hpmcsr
  ecall

after_hpm_alias_\hpmcsr:
  bne   s2, s1, fail
  li    t0, (1 << \idx)
  csrc  mcountinhibit, t0

skip_hpm_alias_\hpmcsr:
.endm

# -----------------------------------------------------------------------
#  Main Verification Blocks
# -----------------------------------------------------------------------

RVTEST_RV32M
RVTEST_CODE_BEGIN

  la   t0, mtvec_handler
  csrw mtvec, t0

  # Verify default power - on reset state
  csrr  t0, mcounteren
  bnez  t0, fail

  # Verify that we can write to mcounteren and read back the expected value
  li    t0, 0x1
  csrw  mcounteren, t0
  csrr  t1, mcounteren
  bne   t1, t0, fail

  # Verify time enable bit is hardwired to zero while other bits are sticky
  li    t0, 0x7
  csrw  mcounteren, t0
  csrr  t1, mcounteren
  xori  t1, t1, 0x5
  bnez  t1, fail

  # Sweep with all implemented counters enabled
  li    t0, 0xFFFFFFFF
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep with all counters disabled
  csrwi mcounteren, 0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep using alternating bits
  li    t0, 0x55555555
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep using arbitrary custom mask
  li    t0, 0xCD609E2D
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Re-enable all counters and verify U-mode CSRs alias their M-mode counterparts.
  li    t0, 0xFFFFFFFF
  csrw  mcounteren, t0
  csrr  s0, mcounteren
  jal   ra, check_counter_aliases

  # If execution hits this line, all pattern sweeps successfully completed
  csrwi mcounteren, 0
  j     pass

  TEST_PASSFAIL

# -----------------------------------------------------------------------
#  Evaluation Subroutine
# -----------------------------------------------------------------------
run_all_csr_tests:
  mv    s3, ra
  la    s5, post_all_tests
  # Drop to U-mode once per pattern to execute the continuous instruction stream
  SWITCH_TO_U_MODE_LABEL(u_mode_sweep_entry)

.balign 4
u_mode_sweep_entry:
  RUN_ALL_CSR_TESTS

  # Reaching this line implies all 32 checks passed cleanly
  ecall

post_all_tests:
  mv    ra, s3
  ret

# -----------------------------------------------------------------------
#  Counter Alias Verification Subroutine
# -----------------------------------------------------------------------
# Verifies that the user-mode counter CSRs alias their M-mode counterparts.
# cycle is checked by the cosim.
check_counter_aliases:
  mv    s3, ra

  # Custom minstret test
  # instret should be exactly 2 more than minstret.
  csrr  t0, minstret
  nop
  csrr  t1, instret
  addi  t2, t0, 2
  bne   t1, t2, fail

  # Reset minstret to zero. The write should suppress the automatic retirement
  # increment, so the immediate read-back will be 0. Reading instret next counts
  # the one csr read.
  csrwi minstret, 0
  csrr  t0, minstret
  csrr  t1, instret
  bnez  t0, fail
  li    t2, 1
  bne   t1, t2, fail

  # HPM alias: iterate over each HPM counter (bits 3-31) that mcounteren
  # reports as implemented. Each counter is frozen with mcountinhibit, set to a
  # value through the m-mode counter, and read back via the U-mode alias CSR.
  CHECK_HPM_ALIAS_ONE  3, mhpmcounter3,   hpmcounter3
  CHECK_HPM_ALIAS_ONE  4, mhpmcounter4,   hpmcounter4
  CHECK_HPM_ALIAS_ONE  5, mhpmcounter5,   hpmcounter5
  CHECK_HPM_ALIAS_ONE  6, mhpmcounter6,   hpmcounter6
  CHECK_HPM_ALIAS_ONE  7, mhpmcounter7,   hpmcounter7
  CHECK_HPM_ALIAS_ONE  8, mhpmcounter8,   hpmcounter8
  CHECK_HPM_ALIAS_ONE  9, mhpmcounter9,   hpmcounter9
  CHECK_HPM_ALIAS_ONE 10, mhpmcounter10,  hpmcounter10
  CHECK_HPM_ALIAS_ONE 11, mhpmcounter11,  hpmcounter11
  CHECK_HPM_ALIAS_ONE 12, mhpmcounter12,  hpmcounter12
  CHECK_HPM_ALIAS_ONE 13, mhpmcounter13,  hpmcounter13
  CHECK_HPM_ALIAS_ONE 14, mhpmcounter14,  hpmcounter14
  CHECK_HPM_ALIAS_ONE 15, mhpmcounter15,  hpmcounter15
  CHECK_HPM_ALIAS_ONE 16, mhpmcounter16,  hpmcounter16
  CHECK_HPM_ALIAS_ONE 17, mhpmcounter17,  hpmcounter17
  CHECK_HPM_ALIAS_ONE 18, mhpmcounter18,  hpmcounter18
  CHECK_HPM_ALIAS_ONE 19, mhpmcounter19,  hpmcounter19
  CHECK_HPM_ALIAS_ONE 20, mhpmcounter20,  hpmcounter20
  CHECK_HPM_ALIAS_ONE 21, mhpmcounter21,  hpmcounter21
  CHECK_HPM_ALIAS_ONE 22, mhpmcounter22,  hpmcounter22
  CHECK_HPM_ALIAS_ONE 23, mhpmcounter23,  hpmcounter23
  CHECK_HPM_ALIAS_ONE 24, mhpmcounter24,  hpmcounter24
  CHECK_HPM_ALIAS_ONE 25, mhpmcounter25,  hpmcounter25
  CHECK_HPM_ALIAS_ONE 26, mhpmcounter26,  hpmcounter26
  CHECK_HPM_ALIAS_ONE 27, mhpmcounter27,  hpmcounter27
  CHECK_HPM_ALIAS_ONE 28, mhpmcounter28,  hpmcounter28
  CHECK_HPM_ALIAS_ONE 29, mhpmcounter29,  hpmcounter29
  CHECK_HPM_ALIAS_ONE 30, mhpmcounter30,  hpmcounter30
  CHECK_HPM_ALIAS_ONE 31, mhpmcounter31,  hpmcounter31
  CHECK_HPM_ALIAS_ONE  3, mhpmcounter3h,  hpmcounter3h
  CHECK_HPM_ALIAS_ONE  4, mhpmcounter4h,  hpmcounter4h
  CHECK_HPM_ALIAS_ONE  5, mhpmcounter5h,  hpmcounter5h
  CHECK_HPM_ALIAS_ONE  6, mhpmcounter6h,  hpmcounter6h
  CHECK_HPM_ALIAS_ONE  7, mhpmcounter7h,  hpmcounter7h
  CHECK_HPM_ALIAS_ONE  8, mhpmcounter8h,  hpmcounter8h
  CHECK_HPM_ALIAS_ONE  9, mhpmcounter9h,  hpmcounter9h
  CHECK_HPM_ALIAS_ONE 10, mhpmcounter10h, hpmcounter10h
  CHECK_HPM_ALIAS_ONE 11, mhpmcounter11h, hpmcounter11h
  CHECK_HPM_ALIAS_ONE 12, mhpmcounter12h, hpmcounter12h
  CHECK_HPM_ALIAS_ONE 13, mhpmcounter13h, hpmcounter13h
  CHECK_HPM_ALIAS_ONE 14, mhpmcounter14h, hpmcounter14h
  CHECK_HPM_ALIAS_ONE 15, mhpmcounter15h, hpmcounter15h
  CHECK_HPM_ALIAS_ONE 16, mhpmcounter16h, hpmcounter16h
  CHECK_HPM_ALIAS_ONE 17, mhpmcounter17h, hpmcounter17h
  CHECK_HPM_ALIAS_ONE 18, mhpmcounter18h, hpmcounter18h
  CHECK_HPM_ALIAS_ONE 19, mhpmcounter19h, hpmcounter19h
  CHECK_HPM_ALIAS_ONE 20, mhpmcounter20h, hpmcounter20h
  CHECK_HPM_ALIAS_ONE 21, mhpmcounter21h, hpmcounter21h
  CHECK_HPM_ALIAS_ONE 22, mhpmcounter22h, hpmcounter22h
  CHECK_HPM_ALIAS_ONE 23, mhpmcounter23h, hpmcounter23h
  CHECK_HPM_ALIAS_ONE 24, mhpmcounter24h, hpmcounter24h
  CHECK_HPM_ALIAS_ONE 25, mhpmcounter25h, hpmcounter25h
  CHECK_HPM_ALIAS_ONE 26, mhpmcounter26h, hpmcounter26h
  CHECK_HPM_ALIAS_ONE 27, mhpmcounter27h, hpmcounter27h
  CHECK_HPM_ALIAS_ONE 28, mhpmcounter28h, hpmcounter28h
  CHECK_HPM_ALIAS_ONE 29, mhpmcounter29h, hpmcounter29h
  CHECK_HPM_ALIAS_ONE 30, mhpmcounter30h, hpmcounter30h
  CHECK_HPM_ALIAS_ONE 31, mhpmcounter31h, hpmcounter31h

  mv    ra, s3
  ret

# -----------------------------------------------------------------------
#  Exception Trap Handler
# -----------------------------------------------------------------------
.balign 256
mtvec_handler:
  csrr  t0, mcause

  # mcause 8 = Environment Call from U-mode (stream finished successfully)
  li    t1, 8
  beq   t0, t1, handle_ecall

  # mcause 2 = Illegal Instruction
  li    t1, 2
  # Drop out to failure trap on all unexpected exceptions
  bne   t0, t1, fail

  # If the register was supposed to be accessible (s1 == 1) but faulted, fail
  bnez  s1, fail

  # Valid hardware restriction exception. Safely continue to next macro block
  csrw  mepc, s4
  mret

handle_ecall:
  # All unrolled checks passed. Safely return back to M-mode context runner
  csrw  mepc, s5
  li    t0, 0x1800
  csrs  mstatus, t0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
