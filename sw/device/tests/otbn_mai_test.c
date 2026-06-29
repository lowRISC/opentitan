// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test runs an OTBN program that exercises the OTBN Masked Arithmetic
// Interface (MAI). It tests two operations:
//   - A B2A conversion followed by an A2B conversion, which must return the
//     secret unchanged.
//   - secAdd, a Boolean-masked arithmetic addition of two operands.
// Ibex loads the inputs into OTBN's data memory, runs the program, and checks
// the results.

#include "hw/top/dt/otbn.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTBN_DECLARE_APP_SYMBOLS(mai_tlt_test);
OTBN_DECLARE_SYMBOL_ADDR(mai_tlt_test, secret);
OTBN_DECLARE_SYMBOL_ADDR(mai_tlt_test, operand_a);
OTBN_DECLARE_SYMBOL_ADDR(mai_tlt_test, operand_b);
OTBN_DECLARE_SYMBOL_ADDR(mai_tlt_test, result);
OTBN_DECLARE_SYMBOL_ADDR(mai_tlt_test, result_secadd);

static const otbn_app_t kAppMaiTest = OTBN_APP_T_INIT(mai_tlt_test);
static const otbn_addr_t kSecret = OTBN_ADDR_T_INIT(mai_tlt_test, secret);
static const otbn_addr_t kOperandA = OTBN_ADDR_T_INIT(mai_tlt_test, operand_a);
static const otbn_addr_t kOperandB = OTBN_ADDR_T_INIT(mai_tlt_test, operand_b);
static const otbn_addr_t kResult = OTBN_ADDR_T_INIT(mai_tlt_test, result);
static const otbn_addr_t kResultSecAdd =
    OTBN_ADDR_T_INIT(mai_tlt_test, result_secadd);

static_assert(kDtOtbnCount >= 1,
              "This test requires at least one OTBN instance");

static dt_otbn_t kTestOtbn = (dt_otbn_t)0;

OTTF_DEFINE_TEST_CONFIG();

// The secret to convert stored as little-endian 32-bit words.
static const uint32_t kSecretInput[8] = {
    0x0003a981, 0x00165e68, 0x007b4968, 0x0028b454,
    0x00670489, 0x003f3539, 0x007325a8, 0x004b0797,
};

// After a B2A conversion followed by an A2B conversion the secret must be
// unchanged, so the expected result equals the input.
static const uint32_t kExpectedResult[8] = {
    0x0003a981, 0x00165e68, 0x007b4968, 0x0028b454,
    0x00670489, 0x003f3539, 0x007325a8, 0x004b0797,
};

// The two operands for secAdd, stored as little-endian 32-bit words.
static const uint32_t kOperandAInput[8] = {
    0x00000001, 0x00100000, 0x00200000, 0x00300000,
    0x00400000, 0x00010203, 0x00040506, 0x0000abcd,
};
static const uint32_t kOperandBInput[8] = {
    0x00000002, 0x00100000, 0x00080000, 0x00040000,
    0x00010000, 0x00010101, 0x00000a0b, 0x00001111,
};

// secAdd adds the operands element-wise (mod 2^32).
static const uint32_t kExpectedSecAdd[8] = {
    0x00000003, 0x00200000, 0x00280000, 0x00340000,
    0x00410000, 0x00020304, 0x00040f11, 0x0000bcde,
};

bool test_main(void) {
  // OTBN needs entropy for the URND WSR that is used to mask the inputs.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // Load the OTBN program
  dif_otbn_t otbn;
  CHECK_DIF_OK(dif_otbn_init_from_dt(kTestOtbn, &otbn));
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kAppMaiTest));

  // Load the inputs into DMEM.
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kSecretInput),
                                            kSecretInput, kSecret));
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kOperandAInput),
                                            kOperandAInput, kOperandA));
  CHECK_STATUS_OK(otbn_testutils_write_data(&otbn, sizeof(kOperandBInput),
                                            kOperandBInput, kOperandB));

  // Run the program and wait for it to finish without errors.
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  // Read the results out of OTBN DMEM and compare them against the expected
  // values.
  uint32_t result[8];
  CHECK_STATUS_OK(
      otbn_testutils_read_data(&otbn, sizeof(result), kResult, result));
  CHECK_ARRAYS_EQ(result, kExpectedResult, ARRAYSIZE(result));

  uint32_t result_secadd[8];
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(result_secadd),
                                           kResultSecAdd, result_secadd));
  CHECK_ARRAYS_EQ(result_secadd, kExpectedSecAdd, ARRAYSIZE(result_secadd));

  return true;
}
