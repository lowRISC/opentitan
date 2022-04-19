// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(barrett384);

static const otbn_app_t kAppBarrett = OTBN_APP_T_INIT(barrett384);

OTBN_DECLARE_APP_SYMBOLS(err_test);

static const otbn_app_t kAppErrTest = OTBN_APP_T_INIT(err_test);

const test_config_t kTestConfig;

/**
 * Get OTBN error bits, check this succeeds and code matches `expected_err_bits`
 */
static void check_otbn_err_bits(otbn_t *otbn_ctx,
                                dif_otbn_err_bits_t expected_err_bits) {
  dif_otbn_err_bits_t otbn_err_bits;
  CHECK_DIF_OK(dif_otbn_get_err_bits(&otbn_ctx->dif, &otbn_err_bits));
  CHECK(otbn_err_bits == expected_err_bits,
        "dif_otbn_get_err_bits() produced unexpected error bits: %x",
        otbn_err_bits);
}

/**
 * Gets the OTBN instruction count, checks that it matches expectations.
 */
static void check_otbn_insn_cnt(otbn_t *otbn_ctx, uint32_t expected_insn_cnt) {
  uint32_t insn_cnt;
  CHECK_DIF_OK(dif_otbn_get_insn_cnt(&otbn_ctx->dif, &insn_cnt));
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
static void test_barrett384(otbn_t *otbn_ctx) {
  enum { kDataSizeBytes = 48 };

  CHECK(otbn_zero_data_memory(otbn_ctx) == kOtbnOk);
  CHECK(otbn_load_app(otbn_ctx, kAppBarrett) == kOtbnOk);

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

  // TODO: Use symbols from the application to load these parameters once they
  // are available (#3998).
  CHECK_DIF_OK(
      dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/0, &a, sizeof(a)));
  CHECK_DIF_OK(
      dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/64, &b, sizeof(b)));
  CHECK_DIF_OK(
      dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/256, &m, sizeof(m)));
  CHECK_DIF_OK(
      dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/320, &u, sizeof(u)));

  CHECK(dif_otbn_set_ctrl_software_errs_fatal(&otbn_ctx->dif, true) == kDifOk);
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  CHECK(dif_otbn_set_ctrl_software_errs_fatal(&otbn_ctx->dif, false) ==
        kDifUnavailable);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  // Reading back result (c).
  dif_otbn_dmem_read(&otbn_ctx->dif, 512, &c, sizeof(c));

  for (int i = 0; i < sizeof(c); ++i) {
    CHECK(c[i] == c_expected[i],
          "Unexpected result c at byte %d: 0x%x (actual) != 0x%x (expected)", i,
          c[i], c_expected[i]);
  }

  check_otbn_insn_cnt(otbn_ctx, 161);
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
static void test_err_test(otbn_t *otbn_ctx) {
  CHECK(otbn_load_app(otbn_ctx, kAppErrTest) == kOtbnOk);

  // TODO: Turn on software_errs_fatal for err_test. Currently the model doesn't
  // support this feature so turning it on leads to a failure when run with the
  // model.
  CHECK(dif_otbn_set_ctrl_software_errs_fatal(&otbn_ctx->dif, false) == kDifOk);
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOperationFailed);

  check_otbn_err_bits(otbn_ctx, kDifOtbnErrBitsBadDataAddr);

  check_otbn_insn_cnt(otbn_ctx, 1);
}

static void test_sec_wipe(otbn_t *otbn_ctx) {
  dif_otbn_status_t otbn_status;

  CHECK(dif_otbn_write_cmd(&otbn_ctx->dif, kDifOtbnCmdSecWipeDmem) == kDifOk);
  CHECK(dif_otbn_get_status(&otbn_ctx->dif, &otbn_status) == kDifOk);
  CHECK(otbn_status == kDifOtbnStatusBusySecWipeDmem);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  CHECK(dif_otbn_write_cmd(&otbn_ctx->dif, kDifOtbnCmdSecWipeImem) == kDifOk);
  CHECK(dif_otbn_get_status(&otbn_ctx->dif, &otbn_status) == kDifOk);
  CHECK(otbn_status == kDifOtbnStatusBusySecWipeImem);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);
}

bool test_main() {
  entropy_testutils_boot_mode_init();

  otbn_t otbn_ctx;
  CHECK(otbn_init(&otbn_ctx, mmio_region_from_addr(
                                 TOP_EARLGREY_OTBN_BASE_ADDR)) == kOtbnOk);

  test_barrett384(&otbn_ctx);
  test_sec_wipe(&otbn_ctx);
  test_err_test(&otbn_ctx);

  return true;
}
