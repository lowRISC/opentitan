// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 12,
  /**
   * The number of attemps for performing operations before timing out.
   */
  kKatTestTimeoutAttempts = 256,
};

/**
 * Cleanly disables the SHA3 conditioner while in SHA3 mode, prompting
 * the release of a conditioned seed.
 *
 * If stopping the conditioner fails, due to pending data keep trying for
 * at most kKatTestTimeoutAttempts.
 *
 * @param entropy An entropy source instance.
 */
static void stop_sha3_conditioner(dif_entropy_src_t *entropy_src) {
  uint32_t fail_count = 0;
  dif_result_t op_result;

  do {
    op_result = dif_entropy_src_conditioner_stop(entropy_src);
    if (op_result == kDifIpFifoFull) {
      fail_count++;
      CHECK(fail_count < kKatTestTimeoutAttempts);
    } else {
      CHECK_DIF_OK(op_result);
    }
  } while (op_result == kDifIpFifoFull);
}

/**
 * Flushes any previously absorbed entropy from the SHA3 conditioning block.
 *
 * @param entropy An entropy source instance.
 */
static void flush_sha3_conditioner(dif_entropy_src_t *entropy_src) {
  // Start and stop the conditioner, without adding any new entropy.
  CHECK_DIF_OK(dif_entropy_src_conditioner_start(entropy_src));
  stop_sha3_conditioner(entropy_src);

  int fail_count = 0;

  // Read (and discard) the resulting seed.
  uint32_t got[kEntropyFifoBufferSize];
  for (size_t i = 0; i < ARRAYSIZE(got); ++i) {
    dif_result_t op_result =
        dif_entropy_src_non_blocking_read(entropy_src, &got[i]);
    if (op_result == kDifUnavailable) {
      fail_count++;
      CHECK(fail_count < kKatTestTimeoutAttempts);
    } else {
      CHECK_DIF_OK(op_result);
    }
  }
}

/**
 * Runs known answer test for the entropy_src SHA-3 conditioner.
 *
 * This test uses the following SHA3 CAVP test vector:
 *
 * Msg=a90d2aa5b241e1ca9dab5b6dc05c3e2c93fc5a2210a6315d60f9b791b36b560d70e135ef8e7dba9441b74e53dab0606b
 * MD=4a16881ce156f45fdfdb45088e3f23be1b4c5a7a6a35315d36c51c75f275733319aca185d4ab33130ffe45f751f1bbc5
 *
 * See:
 * https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing
 */
void test_sha384_kat(dif_entropy_src_t *entropy_src) {
  entropy_testutils_stop_all();
  entropy_testutils_fw_override_enable(entropy_src, kEntropyFifoBufferSize,
                                       /*route_to_firmware=*/true,
                                       /*bypass_conditioner=*/false);

  // Though most of the entropy_src state is cleared on disable, the
  // SHA3 conditioner accumulates entropy even from aborted seeds. For
  // the KAT though, we must clear any previously absorbed entropy.
  flush_sha3_conditioner(entropy_src);

  const uint32_t kInputMsg[kEntropyFifoBufferSize] = {
      0xa52a0da9, 0xcae141b2, 0x6d5bab9d, 0x2c3e5cc0, 0x225afc93, 0x5d31a610,
      0x91b7f960, 0x0d566bb3, 0xef35e170, 0x94ba7d8e, 0x534eb741, 0x6b60b0da,
  };

  CHECK_DIF_OK(dif_entropy_src_conditioner_start(entropy_src));

  dif_result_t op_result;
  uint32_t fail_count = 0;
  uint32_t count;
  uint32_t total = 0;

  // Load the input data.
  do {
    op_result = dif_entropy_src_observe_fifo_write(
        entropy_src, kInputMsg + total, ARRAYSIZE(kInputMsg) - total, &count);
    total += count;
    if (op_result == kDifIpFifoFull) {
      fail_count++;
      CHECK(fail_count < kKatTestTimeoutAttempts);
    } else {
      fail_count = 0;
      CHECK_DIF_OK(op_result);
    }
  } while (total < ARRAYSIZE(kInputMsg));

  // Cleanly disable the conditioner.
  stop_sha3_conditioner(entropy_src);

  fail_count = 0;
  uint32_t got[kEntropyFifoBufferSize];
  for (size_t i = 0; i < ARRAYSIZE(got); ++i) {
    op_result = dif_entropy_src_non_blocking_read(entropy_src, &got[i]);
    if (op_result == kDifUnavailable) {
      fail_count++;
      CHECK(fail_count < kKatTestTimeoutAttempts);
    } else {
      CHECK_DIF_OK(op_result);
    }
  }

  const uint32_t kExpectedDigest[kEntropyFifoBufferSize] = {
      0x1c88164a, 0x5ff456e1, 0x0845dbdf, 0xbe233f8e, 0x7a5a4c1b, 0x5d31356a,
      0x751cc536, 0x337375f2, 0x85a1ac19, 0x1333abd4, 0xf745fe0f, 0xc5bbf151,
  };

  CHECK_ARRAYS_EQ(got, kExpectedDigest, kEntropyFifoBufferSize,
                  "Unexpected digest value.");
}

bool test_main(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  test_sha384_kat(&entropy_src);
  return true;
}
