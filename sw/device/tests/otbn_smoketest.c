// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(barrett384);
OTBN_DECLARE_SYMBOL_ADDR(barrett384, inp_a);
OTBN_DECLARE_SYMBOL_ADDR(barrett384, inp_b);
OTBN_DECLARE_SYMBOL_ADDR(barrett384, inp_m);
OTBN_DECLARE_SYMBOL_ADDR(barrett384, inp_u);
OTBN_DECLARE_SYMBOL_ADDR(barrett384, oup_c);

static const otbn_app_t kAppBarrett = OTBN_APP_T_INIT(barrett384);
static const otbn_addr_t kInpA = OTBN_ADDR_T_INIT(barrett384, inp_a);
static const otbn_addr_t kInpB = OTBN_ADDR_T_INIT(barrett384, inp_b);
static const otbn_addr_t kInpM = OTBN_ADDR_T_INIT(barrett384, inp_m);
static const otbn_addr_t kInpU = OTBN_ADDR_T_INIT(barrett384, inp_u);
static const otbn_addr_t kOupC = OTBN_ADDR_T_INIT(barrett384, oup_c);

OTBN_DECLARE_APP_SYMBOLS(err_test);

static const otbn_app_t kAppErrTest = OTBN_APP_T_INIT(err_test);

OTTF_DEFINE_TEST_CONFIG();

/**
 * Gets the OTBN instruction count, checks that it matches expectations.
 */
static void check_otbn_insn_cnt(dif_otbn_t *otbn, uint32_t expected_insn_cnt) {
  uint32_t insn_cnt;
  CHECK_DIF_OK(dif_otbn_get_insn_cnt(otbn, &insn_cnt));
  CHECK(insn_cnt == expected_insn_cnt,
        "Expected to execute %d instructions, but got %d.", expected_insn_cnt,
        insn_cnt);
}

/**
 * Run a 384-bit Barrett Multiplication on OTBN and check its result.
 *
 * This test is not aiming to exhaustively test the Barrett multiplication
 * itself, but test the interaction between device software and OTBN. As such,
 * only trivial parameters are used.
 *
 * The code executed on OTBN can be found in sw/otbn/code-snippets/barrett384.s.
 * The entry point wrap_barrett384() is called according to the calling
 * convention described in the OTBN assembly code file.
 */
static void test_barrett384(dif_otbn_t *otbn) {
  enum { kDataSizeBytes = 48 };

  CHECK_STATUS_OK(otbn_testutils_load_app(otbn, kAppBarrett));

  // a, first operand
  static const uint8_t a[kDataSizeBytes] = {10};

  // b, second operand
  static uint8_t b[kDataSizeBytes] = {20};

  // m, modulus, max. length 384 bit with 2^384 > m > 2^383
  // We choose the modulus of P-384: m = 2**384 - 2**128 - 2**96 + 2**32 - 1
  static const uint8_t m[kDataSizeBytes] = {
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff};

  // u, pre-computed Barrett constant (without u[384]/MSb of u which is always 1
  // for the allowed range but has to be set to 0 here).
  // u has to be pre-calculated as u = floor(2^768/m).
  static const uint8_t u[kDataSizeBytes] = {
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01};

  // c, result, max. length 384 bit.
  uint8_t c[kDataSizeBytes] = {0};

  // c = (a * b) % m = (10 * 20) % m = 200
  static const uint8_t c_expected[kDataSizeBytes] = {200};

  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, sizeof(a), &a, kInpA));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, sizeof(b), &b, kInpB));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, sizeof(m), &m, kInpM));
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, sizeof(u), &u, kInpU));

  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(otbn, true));
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  CHECK(dif_otbn_set_ctrl_software_errs_fatal(otbn, false) == kDifUnavailable);
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));

  // Reading back result (c).
  CHECK_STATUS_OK(otbn_testutils_read_data(otbn, sizeof(c), kOupC, &c));

  for (int i = 0; i < sizeof(c); ++i) {
    CHECK(c[i] == c_expected[i],
          "Unexpected result c at byte %d: 0x%x (actual) != 0x%x (expected)", i,
          c[i], c_expected[i]);
  }

  check_otbn_insn_cnt(otbn, 174);
}

/**
 * Run err_test on OTBN and check it produces the expected error
 *
 * This test tries to load from an invalid address which should result in the
 * kDifOtbnErrBitsBadDataAddr error bit being set
 *
 * The code executed on OTBN can be found in sw/otbn/code-snippets/err_test.s.
 * The entry point wrap_err_test() is called, no arguments are passed or results
 * returned.
 */
static void test_err_test(dif_otbn_t *otbn) {
  CHECK_STATUS_OK(otbn_testutils_load_app(otbn, kAppErrTest));

  // TODO: Turn on software_errs_fatal for err_test. Currently the model doesn't
  // support this feature so turning it on leads to a failure when run with the
  // model.
  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(otbn, false));
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  CHECK_STATUS_OK(
      otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsBadDataAddr));

  check_otbn_insn_cnt(otbn, 1);
}

static void test_sec_wipe(dif_otbn_t *otbn) {
  dif_otbn_status_t otbn_status;

  CHECK_DIF_OK(dif_otbn_write_cmd(otbn, kDifOtbnCmdSecWipeDmem));
  CHECK_DIF_OK(dif_otbn_get_status(otbn, &otbn_status));
  CHECK(otbn_status == kDifOtbnStatusBusySecWipeDmem);
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));

  CHECK_DIF_OK(dif_otbn_write_cmd(otbn, kDifOtbnCmdSecWipeImem));
  CHECK_DIF_OK(dif_otbn_get_status(otbn, &otbn_status));
  CHECK(otbn_status == kDifOtbnStatusBusySecWipeImem);
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  dif_otbn_t otbn;
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  test_barrett384(&otbn);
  test_sec_wipe(&otbn);
  test_err_test(&otbn);

  return true;
}
