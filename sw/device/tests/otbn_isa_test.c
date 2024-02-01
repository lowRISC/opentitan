// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * This test runs every instruction in OTBN's ISA and checks the result.
 *
 * It reuses the `smoke_test.s` script used in OTBN's Design Verification,
 * but with accesses the `RND` and `KEY_*` WSRs removed.
 * The result in `w1` and `w2` are downstream of the `KEY_*`,
 * loads and so are not checked.
 *
 * The zero register and `x1` stack register are ignored.
 */
OTTF_DEFINE_TEST_CONFIG();

OTBN_DECLARE_APP_SYMBOLS(smoke_test);
OTBN_DECLARE_SYMBOL_ADDR(smoke_test, gpr_state);
OTBN_DECLARE_SYMBOL_ADDR(smoke_test, wdr_state);

static const otbn_app_t kAppSmokeTest = OTBN_APP_T_INIT(smoke_test);
static const otbn_addr_t kGprState = OTBN_ADDR_T_INIT(smoke_test, gpr_state);
static const otbn_addr_t kWdrState = OTBN_ADDR_T_INIT(smoke_test, wdr_state);

enum {
  kNumExpectedGprs = 30,
  kNumExpectedWdrs = 32,
  kExpectedInstrCount = 284,
};

// The expected values of the GPRs and WDRs are taken from
// `hw/ip/otbn/dv/smoke/smoke_expected.txt`.
static const uint32_t kExpectedGprs[kNumExpectedGprs] = {
    0xd0beb513, 0xa0be911a, 0x717d462d, 0xcfffdc07, 0xf0beb51b, 0x80be9112,
    0x70002409, 0xd0beb533, 0x00000510, 0xd0beb169, 0xfad44c00, 0x000685f5,
    0xffa17d6a, 0x4c000000, 0x00000034, 0xfffffff4, 0xfacefeed, 0xd0beb533,
    0x00000123, 0x00000123, 0xcafef010, 0x89c9b54f, 0x00000052, 0x00000020,
    0x00000016, 0x0000001a, 0x00400000, 0x00018000, 0x00000000, 0x00000804};

static const uint32_t kExpectedWdrs[kNumExpectedWdrs][8] = {
    [0] = {0x0f09b7c8, 0x25769434, 0x6978ad1b, 0x67a8c221, 0x5466a52c,
           0x73880075, 0xf9dbff5e, 0x37adadae},
    [1] = {0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
           0x00000000, 0x00000000, 0x00000000},
    [2] = {0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
           0x00000000, 0x00000000, 0x00000000},
    [3] = {0xed103473, 0x431165e5, 0x0357f208, 0x7245a2d0, 0x22168ae8,
           0x34745ffa, 0xbbc28370, 0x23a776b0},
    [4] = {0xb9dd0141, 0xedbc1090, 0xd024bed4, 0x1cf04d7a, 0xeee357b5,
           0xdf1f0aa4, 0x888f503c, 0xce52215b},
    [5] = {0xdbff9bdb, 0xbaeebbbb, 0xf9bfd9ff, 0xefbafaaf, 0x99fdf9df,
           0xabebbfef, 0xbbb9f9df, 0xfafeeeae},
    [6] = {0x11109898, 0x8822aa2a, 0x09981808, 0x828aa820, 0x88189108,
           0x8888a00a, 0x00088990, 0x28a88802},
    [7] = {0xcaef0343, 0x32cc1191, 0xf027c1f7, 0x6d30528f, 0x11e568d7,
           0x23631fe5, 0xbbb1704f, 0xd25666ac},
    [8] = {0xac896525, 0x679944c4, 0x9641a791, 0x386507da, 0x77830eb1,
           0x76364ab0, 0xddd71629, 0x870333f9},
    [9] = {0xcccccd55, 0x555554cc, 0xcccccd55, 0x555554cc, 0xb4d6d555,
           0x35d9da9b, 0xf2c374c3, 0xd7c12b4d},
    [10] = {0xf0cd30f0, 0x45114443, 0xd30cf2cd, 0x1045054f, 0x32ced2ed,
            0x54144010, 0x1112d2ed, 0x05011151},
    [11] = {0xbbbc3433, 0x77dd55d5, 0xc334b4c4, 0x7d7557df, 0x44b43bc4,
            0x77775ff5, 0xccc4433c, 0xd75777fd},
    [12] = {0x22229a9a, 0xcd32ab2b, 0x299b1b2a, 0xd2caad35, 0xab1aa22a,
            0xccccb54a, 0x332aa9a2, 0x2caccd53},
    [13] = {0x97ba66a7, 0x20896565, 0xa689a3aa, 0x4a25a045, 0x43c8b58a,
            0x1252555a, 0x5564a69a, 0xa1a55408},
    [14] = {0x7956327a, 0xbcee9991, 0x630e74e6, 0x8dba5ca7, 0x2c59e406,
            0xac10254c, 0xd09a8aec, 0x5ec45f47},
    [15] = {0xac896524, 0xbcee9a19, 0x9641a791, 0x8dba5d2f, 0x77830eb1,
            0xcb8ba005, 0xddd71629, 0xdc58894e},
    [16] = {0xb9dd0141, 0xedbc1090, 0xd024bed4, 0x1cf04d7a, 0xeee357b5,
            0xdf1f0aa4, 0x888f503c, 0xce52215b},
    [17] = {0x33333331, 0x55555555, 0x33333333, 0x55555555, 0x33333333,
            0x55555555, 0x33333333, 0x55555555},
    [18] = {0x53769ada, 0x9866bb3b, 0x69be586e, 0xc79af825, 0x22168a4e,
            0x34745fe9, 0xbbc28381, 0x23a7769f},
    [19] = {0x00000000, 0x00000000, 0x09981800, 0x828aa801, 0x8818910a,
            0x8888a009, 0x00088982, 0x28a88800},
    [20] = {0xb9dd0130, 0xedbc10a1, 0x69be57c3, 0xc79af825, 0x887cf14e,
            0x89c9b54f, 0x2228e9d6, 0x78fccc06},
    [21] = {0xdbff9bfa, 0xbaeebbbb, 0xf9bfd9ee, 0xefbafabd, 0x887cf1ee,
            0x89c9b54f, 0x2228e9d6, 0x78fccc06},
    [22] = {0xdbff9db7, 0xbaeebbbb, 0xf9bfd9ee, 0xefbafabd, 0x887cf1ee,
            0x89c9b54f, 0x2228e9d6, 0x78fccc06},
    [23] = {0xdbff99f3, 0xbaeebbbb, 0xf9bfd9ee, 0xefbafabd, 0x887cf1ee,
            0x89c9b54f, 0x2228e9d6, 0x78fccc06},
    [24] = {0x1234abcd, 0xd0beb533, 0xcafed00d, 0xdeadbeef, 0xfacefeed,
            0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc},
    [25] = {0x1234abcd, 0xd0beb533, 0xcafed00d, 0xdeadbeef, 0xfacefeed,
            0xaaaaaaaa, 0xbbbbbbbb, 0xcccccccc},
    [26] = {0xdbff9bfa, 0xbaeebbbb, 0xf9bfd9ee, 0xefbafabd, 0x887cf1ee,
            0x89c9b54f, 0x2228e9d6, 0x78fccc06},
    [27] = {0x11109898, 0x8822aa2a, 0x09981808, 0x828aa820, 0x88189108,
            0x8888a00a, 0x00088990, 0x28a88802},
    [28] = {0xcaef0343, 0x32cc1191, 0xf027c1f7, 0x6d30528f, 0x11e568d7,
            0x23631fe5, 0xbbb1704f, 0xd25666ac},
    [29] = {0xeb0953c2, 0xe0654fef, 0x63388709, 0x5763bcdf, 0x26628bdb,
            0x64341d3c, 0x9f24f0c1, 0x4f0d4b81},
    [30] = {0x68ba2fa1, 0xb55098e0, 0x4efa2ec9, 0xaee49292, 0xab123192,
            0xffa3d88b, 0xe9ee7ac7, 0x2167f87d},
    [31] = {0x0f09b7c8, 0x25769434, 0x6978ad1b, 0x67a8c221, 0x5466a52c,
            0x73880075, 0xf9dbff5e, 0x37adadae},
};

bool test_main(void) {
  // Initialise the entropy source and OTBN
  dif_otbn_t otbn;
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Load the Smoke Test App
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kAppSmokeTest));
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  // Check the instruction count is what was expected.
  uint32_t instruction_count;
  CHECK_DIF_OK(dif_otbn_get_insn_cnt(&otbn, &instruction_count));
  CHECK(kExpectedInstrCount == instruction_count,
        "Expected OTBN to execute %d instructions, but it exected %d",
        kExpectedInstrCount, instruction_count);

  // Check the GPR registers of interest hold the expected values.
  uint32_t gpr_state[kNumExpectedGprs];
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(kExpectedGprs),
                                           kGprState, &gpr_state));
  CHECK_ARRAYS_EQ(gpr_state, kExpectedGprs, kNumExpectedGprs);

  // Check the WDR registers of interest hold the expected values.
  uint32_t wdr_state[kNumExpectedWdrs][8];
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(kExpectedWdrs),
                                           kWdrState, &wdr_state));

  CHECK_ARRAYS_EQ(wdr_state[0], kExpectedWdrs[0], 8,
                  "w0 didn't match the expected value.");
  // We ignore register w1 and w2.
  for (size_t i = 3; i < kNumExpectedWdrs; ++i) {
    CHECK_ARRAYS_EQ(wdr_state[i], kExpectedWdrs[i], 8,
                    "w%d didn't match the expected value.", i);
  };
  return true;
}
