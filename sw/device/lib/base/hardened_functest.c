// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

status_t good_eq_test(void) {
  uint32_t a = 100, b = 100;
  HARDENED_CHECK_EQ(a, b);
  return OK_STATUS();
}
status_t good_ne_test(void) {
  uint32_t a = 100, b = 150;
  HARDENED_CHECK_NE(a, b);
  return OK_STATUS();
}
status_t good_lt_test(void) {
  uint32_t a = 100, b = 150;
  HARDENED_CHECK_LT(a, b);
  return OK_STATUS();
}
status_t good_gt_test(void) {
  uint32_t a = 150, b = 100;
  HARDENED_CHECK_GT(a, b);
  return OK_STATUS();
}
status_t good_le_test(void) {
  uint32_t a = 100, b = 100;
  HARDENED_CHECK_LE(a, b);
  HARDENED_CHECK_LE(a, b + 1);
  return OK_STATUS();
}
status_t good_ge_test(void) {
  uint32_t a = 100, b = 100;
  HARDENED_CHECK_GE(a, b);
  HARDENED_CHECK_GE(a + 1, b);
  return OK_STATUS();
}

uint32_t exc_seen;
void ottf_illegal_instr_fault_handler(uint32_t *exc_info) {
  switch (exc_seen) {
    case 0:
      // The first exception is when we hit `unimp` after failing the first
      // comparison in the hardenend check. The exception handler has
      // already computed the correct return PC for us, so we can simply
      // increment the state and return.  This will cause execution to
      // continue at the inverted compare/branch instruction in the hardened
      // sequence.  The comparison will succeed and branch back to the
      // `unimp` instruction.  This will re-invoke this fault handler in the
      // next state.
      exc_seen += 1;
      return;
    case 1:
      // The second exception is when we hit `unimp` after failing the second
      // comparison in the hardenend check.
      exc_seen += 1;
      // Jump the PC over the comparison so we can exit the test function.  In
      // this case, the PC is again pointing at the inverse compare/branch after
      // the `unimp` instruction.  Since that instruction is 4 bytes, increment
      // the PC by 4.  In the exception frame, the return PC is the zeroth word.
      exc_info[0] += 4;
      return;
    default:
      // In all other cases, we are in an invalid test state.  Invoke the
      // generic fault handler.
      ottf_generic_fault_print(exc_info, "Illegal Instruction",
                               ibex_mcause_read());
      abort();
  }
}

status_t bad_eq_test(void) {
  uint32_t a = 100, b = 199;
  exc_seen = 0;
  HARDENED_CHECK_EQ(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}
status_t bad_ne_test(void) {
  uint32_t a = 100, b = 100;
  exc_seen = 0;
  HARDENED_CHECK_NE(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}
status_t bad_lt_test(void) {
  uint32_t a = 199, b = 100;
  exc_seen = 0;
  HARDENED_CHECK_LT(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}
status_t bad_gt_test(void) {
  uint32_t a = 100, b = 199;
  exc_seen = 0;
  HARDENED_CHECK_GT(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}
status_t bad_le_test(void) {
  uint32_t a = 199, b = 100;
  exc_seen = 0;
  HARDENED_CHECK_LE(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}
status_t bad_ge_test(void) {
  uint32_t a = 100, b = 199;
  exc_seen = 0;
  HARDENED_CHECK_GE(a, b);
  return exc_seen == 2 ? OK_STATUS() : UNKNOWN();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  // Test each hardened check when the check is valid.
  EXECUTE_TEST(result, good_eq_test);
  EXECUTE_TEST(result, good_ne_test);
  EXECUTE_TEST(result, good_lt_test);
  EXECUTE_TEST(result, good_gt_test);
  EXECUTE_TEST(result, good_le_test);
  EXECUTE_TEST(result, good_ge_test);

  // Test each hardened check when the check is invalid.
  // Each of these tests is expected to hit the `unimp` instruction in the
  // hardended sequence twice.  The exception handler will guide the test
  // through the hardened check so that we know we've examined both
  // compare/branch instructions in the hardened sequence.
  EXECUTE_TEST(result, bad_eq_test);
  EXECUTE_TEST(result, bad_ne_test);
  EXECUTE_TEST(result, bad_lt_test);
  EXECUTE_TEST(result, bad_gt_test);
  EXECUTE_TEST(result, bad_le_test);
  EXECUTE_TEST(result, bad_ge_test);
  return status_ok(result);
}
