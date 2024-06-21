// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_clkmgr_t clkmgr;
static dif_kmac_t kmac;

OTTF_DEFINE_TEST_CONFIG();

const dif_clkmgr_hintable_clock_t kmac_clock =
    kTopEarlgreyHintableClocksMainKmac;

#define TIMEOUT (1000 * 1000)

// Digest lengths in 32-bit words.
#define DIGEST_LEN_SHA3_256 (256 / 32)
#define DIGEST_LEN_SHA3_512 (512 / 32)
#define DIGEST_LEN_SHA3_MAX DIGEST_LEN_SHA3_512

// SHA-3 test description.
typedef struct sha3_test {
  dif_kmac_mode_sha3_t mode;

  const char *message;
  size_t message_len;

  const uint32_t digest[DIGEST_LEN_SHA3_MAX];
  size_t digest_len;
} sha3_test_t;

// SHA-3 test.
const sha3_test_t sha3_256_test = {
    // Example taken from NIST FIPS-202 Algorithm Test Vectors:
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
    .mode = kDifKmacModeSha3Len256,
    .message = "\xe7\x37\x21\x05",
    .message_len = 4,
    .digest = {0x8ab6423a, 0x8cf279b0, 0x52c7a34c, 0x90276f29, 0x78fec406,
               0xd979ebb1, 0x057f7789, 0xae46401e},
    .digest_len = DIGEST_LEN_SHA3_256};

static void check_clock_state(dif_toggle_t expected_clock_state) {
  dif_toggle_t clock_state;
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_get_enabled(&clkmgr, kmac_clock, &clock_state));
  CHECK(clock_state == expected_clock_state,
        "Clock enabled state is not as expected (%d).", expected_clock_state);
}

static bool is_hintable_clock_enabled(const dif_clkmgr_t *clkmgr,
                                      dif_clkmgr_hintable_clock_t clock) {
  dif_toggle_t clock_state;
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_get_enabled(clkmgr, clock, &clock_state));
  return clock_state == kDifToggleEnabled;
}

static void do_sha3_test(void) {
  dif_kmac_operation_state_t kmac_operation_state;
  // Run SHA3 test case using single blocking absorb/squeeze operations.
  CHECK_DIF_OK(dif_kmac_mode_sha3_start(&kmac, &kmac_operation_state,
                                        sha3_256_test.mode));

  // Set hint and check clk state remains enabled as KMAC is now not idle.
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kmac_clock,
                                                  kDifToggleDisabled));
  check_clock_state(kDifToggleEnabled);

  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state,
                               sha3_256_test.message, sha3_256_test.message_len,
                               NULL));

  uint32_t out[DIGEST_LEN_SHA3_MAX];
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &kmac_operation_state, out,
                                sha3_256_test.digest_len, /*processed=*/NULL,
                                /*capacity=*/NULL));

  // Check clock state again which should still be enabled.
  check_clock_state(kDifToggleEnabled);

  CHECK_DIF_OK(dif_kmac_end(&kmac, &kmac_operation_state));

  // On FPGA, it may take a while until the DONE command gets actually executed
  // (see SecCmdDelay SystemVerilog parameter). However, once the clock is
  // disabled, KMAC cannot be accessed anymore. Thus polling the KMAC status
  // register doesn't work. Instead, wait for the clock to stop.
  IBEX_SPIN_FOR(!is_hintable_clock_enabled(&clkmgr, kmac_clock), TIMEOUT);

  // Check the clock is now stopped.
  check_clock_state(kDifToggleDisabled);

  // Check the result to be sure the SHA3 operation completed correctly.
  CHECK_ARRAYS_EQ(out, sha3_256_test.digest, sha3_256_test.digest_len,
                  "Digest mismatch for test SHA3 256.");

  // Set hint to enabled again to check that clock can be re-enabled.
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kmac_clock,
                                                  kDifToggleEnabled));
  check_clock_state(kDifToggleEnabled);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  // Get initial hint and enable for KMAC clock and check both are enabled.
  dif_toggle_t clock_hint_state;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(&clkmgr, kmac_clock,
                                                  &clock_hint_state));
  CHECK(clock_hint_state == kDifToggleEnabled);
  check_clock_state(kDifToggleEnabled);

  // While KMAC is not in use, set disabled hint for KMAC clock
  // then check clock state, set back to enabled and check again.
  // Note: disabled means the clock can be disabled.
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kmac_clock,
                                                  kDifToggleDisabled));
  check_clock_state(kDifToggleDisabled);
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(&clkmgr, kmac_clock,
                                                  kDifToggleEnabled));
  check_clock_state(kDifToggleEnabled);

  // Initialize KMAC hardware.
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  // call sha3 test twice to check that when clock
  // is enabled again after the first call
  // that all still works for the second call.

  do_sha3_test();
  do_sha3_test();

  return true;
}
