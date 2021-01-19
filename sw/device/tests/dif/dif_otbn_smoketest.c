// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTBN_DECLARE_APP_SYMBOLS(barrett384);
OTBN_DECLARE_PTR_SYMBOL(barrett384, wrap_barrett384);

static const otbn_app_t kAppBarrett = OTBN_APP_T_INIT(barrett384);
static const otbn_ptr_t kFuncWrapBarrett384 =
    OTBN_PTR_T_INIT(barrett384, wrap_barrett384);

OTBN_DECLARE_APP_SYMBOLS(err_test);
OTBN_DECLARE_PTR_SYMBOL(err_test, err_test);

static const otbn_app_t kAppErrTest = OTBN_APP_T_INIT(err_test);
static const otbn_ptr_t kFuncWrapErrTest = OTBN_PTR_T_INIT(err_test, err_test);

const test_config_t kTestConfig;

/**
 * Get OTBN error bits, check this succeeds and code matches `expected_err_bits`
 */
static void check_otbn_err_bits(otbn_t *otbn_ctx,
                                dif_otbn_err_bits_t expected_err_bits) {
  dif_otbn_err_bits_t otbn_err_bits;
  dif_otbn_result_t rv = dif_otbn_get_err_bits(&otbn_ctx->dif, &otbn_err_bits);
  CHECK(rv == kDifOtbnOk, "dif_otbn_get_err_bits() failed: %d", rv);
  CHECK(otbn_err_bits == expected_err_bits,
        "dif_otbn_get_err_bits() produced unexpected error bits: %x",
        otbn_err_bits);
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
  CHECK(dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/0, &a,
                            sizeof(a)) == kDifOtbnOk);
  CHECK(dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/64, &b,
                            sizeof(b)) == kDifOtbnOk);
  CHECK(dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/256, &m,
                            sizeof(m)) == kDifOtbnOk);
  CHECK(dif_otbn_dmem_write(&otbn_ctx->dif, /*offset_bytes=*/320, &u,
                            sizeof(u)) == kDifOtbnOk);

  CHECK(otbn_call_function(otbn_ctx, kFuncWrapBarrett384) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  // Reading back result (c).
  dif_otbn_dmem_read(&otbn_ctx->dif, 512, &c, sizeof(c));

  for (int i = 0; i < sizeof(c); ++i) {
    CHECK(c[i] == c_expected[i],
          "Unexpected result c at byte %d: 0x%x (actual) != 0x%x (expected)", i,
          c[i], c_expected[i]);
  }
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

  CHECK(otbn_call_function(otbn_ctx, kFuncWrapErrTest) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnExecutionFailed);

  check_otbn_err_bits(otbn_ctx, kDifOtbnErrBitsBadDataAddr);
}

bool test_main() {
  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };

  otbn_t otbn_ctx;
  CHECK(otbn_init(&otbn_ctx, otbn_config) == kOtbnOk);

  test_barrett384(&otbn_ctx);
  test_err_test(&otbn_ctx);

  return true;
}
