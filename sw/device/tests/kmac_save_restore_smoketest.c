// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/kmac.h"  // Generated
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static const dt_kmac_t kKmacDt = (dt_kmac_t)0;

enum {
  /**
   * The largest Keccak rate of the modes under test, in bytes.
   */
  kMaxBlockLen = 168,

  /**
   * Length of the message part that is absorbed after the context has been
   * restored. This part does not need to be block aligned.
   */
  kTailLen = 37,

  kMaxMessageLen = kMaxBlockLen + kTailLen,

  /**
   * Digest length in 32-bit words.
   */
  kDigestLen = 8,
};

/**
 * The hashing mode a test case runs in.
 */
typedef enum sr_mode {
  kSrModeSha3,
  kSrModeCshake,
  kSrModeKmac,
} sr_mode_t;

/**
 * Save and restore test case description.
 *
 * The modes differ in what the continue command has to skip: cSHAKE and KMAC
 * prepend a prefix block, KMAC additionally prepends the secret key block. The
 * Keccak rate differs as well, which determines where a context can be saved.
 */
typedef struct sr_test {
  const char *name;
  sr_mode_t mode;

  /**
   * The Keccak rate in bytes. A context can only be saved after a multiple of
   * this many message bytes have been absorbed.
   */
  size_t block_len;
} sr_test_t;

const sr_test_t kSrTests[] = {
    {
        .name = "SHA3-256",
        .mode = kSrModeSha3,
        .block_len = 136,
    },
    {
        .name = "cSHAKE128",
        .mode = kSrModeCshake,
        .block_len = 168,
    },
    {
        .name = "KMAC128",
        .mode = kSrModeKmac,
        .block_len = 168,
    },
};

static const dif_kmac_key_t kKey = {
    .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C, 0x53525150,
               0x57565554, 0x5B5A5958, 0x5F5E5D5C},
    .share1 = {0},
    .length = kDifKmacKeyLen256,
};

static dif_kmac_t kmac;

/**
 * Fill a message buffer with a seed dependent pattern.
 */
static void message_init(uint8_t *msg, size_t len, uint8_t seed) {
  for (size_t i = 0; i < len; ++i) {
    msg[i] = (uint8_t)(seed + i * 7);
  }
}

/**
 * Start an operation in the mode of the given test case.
 */
static void start_operation(const sr_test_t *test,
                            dif_kmac_operation_state_t *op_state) {
  switch (test->mode) {
    case kSrModeSha3:
      CHECK_DIF_OK(
          dif_kmac_mode_sha3_start(&kmac, op_state, kDifKmacModeSha3Len256));
      break;
    case kSrModeCshake: {
      dif_kmac_function_name_t n;
      CHECK_DIF_OK(dif_kmac_function_name_init("SR", 2, &n));
      CHECK_DIF_OK(dif_kmac_mode_cshake_start(
          &kmac, op_state, kDifKmacModeCshakeLen128, &n, NULL));
      break;
    }
    case kSrModeKmac:
      CHECK_DIF_OK(dif_kmac_mode_kmac_start(
          &kmac, op_state, kDifKmacModeKmacLen128, kDigestLen, &kKey, NULL));
      break;
    default:
      CHECK(false, "unknown mode");
  }
}

/**
 * Hash a message in a single operation. This is the reference the save and
 * restore results are compared against.
 */
static void hash_whole(const sr_test_t *test, const uint8_t *msg,
                       size_t msg_len, uint32_t *digest) {
  dif_kmac_operation_state_t op_state;

  start_operation(test, &op_state);
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, msg, msg_len, NULL));
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &op_state, digest, kDigestLen,
                                /*processed=*/NULL, /*capacity=*/NULL));
  CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));
}

/**
 * Compare a digest against the reference digest.
 */
static void check_digest(const sr_test_t *test, const char *what,
                         const uint32_t *got, const uint32_t *want) {
  for (size_t i = 0; i < kDigestLen; ++i) {
    CHECK(got[i] == want[i], "%s %s: mismatch at %d got=0x%08x want=0x%08x",
          test->name, what, i, got[i], want[i]);
  }
}

/**
 * Absorb a message in two parts, saving and immediately restoring the context
 * in between. The result must match the message hashed in one operation.
 */
static void test_save_restore(const sr_test_t *test) {
  uint8_t msg[kMaxMessageLen];
  size_t msg_len = test->block_len + kTailLen;
  message_init(msg, msg_len, 0x5a);

  uint32_t want[kDigestLen];
  hash_whole(test, msg, msg_len, want);

  dif_kmac_operation_state_t op_state;
  dif_kmac_context_t context;

  // Absorb one complete block, then save the context.
  start_operation(test, &op_state);
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, msg, test->block_len, NULL));
  CHECK_DIF_OK(dif_kmac_context_save(&kmac, &op_state, &context));

  // Restore the context and absorb the rest of the message.
  CHECK_DIF_OK(dif_kmac_context_restore(&kmac, &context, &op_state));
  CHECK_DIF_OK(
      dif_kmac_absorb(&kmac, &op_state, &msg[test->block_len], kTailLen, NULL));

  uint32_t got[kDigestLen];
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &op_state, got, kDigestLen,
                                /*processed=*/NULL, /*capacity=*/NULL));
  CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

  check_digest(test, "save and restore", got, want);
}

/**
 * Interleave two message streams. Both contexts are saved before either one is
 * restored, so the second operation runs while the first context is held in
 * software.
 */
static void test_interleaved(const sr_test_t *test) {
  uint8_t msg_a[kMaxMessageLen];
  uint8_t msg_b[kMaxMessageLen];
  size_t msg_len = test->block_len + kTailLen;
  message_init(msg_a, msg_len, 0x11);
  message_init(msg_b, msg_len, 0x22);

  uint32_t want_a[kDigestLen];
  uint32_t want_b[kDigestLen];
  hash_whole(test, msg_a, msg_len, want_a);
  hash_whole(test, msg_b, msg_len, want_b);

  dif_kmac_operation_state_t op_state;
  dif_kmac_context_t context_a;
  dif_kmac_context_t context_b;

  // Save the context of stream A.
  start_operation(test, &op_state);
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, msg_a, test->block_len, NULL));
  CHECK_DIF_OK(dif_kmac_context_save(&kmac, &op_state, &context_a));

  // Save the context of stream B.
  start_operation(test, &op_state);
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, msg_b, test->block_len, NULL));
  CHECK_DIF_OK(dif_kmac_context_save(&kmac, &op_state, &context_b));

  // Complete stream A.
  uint32_t got_a[kDigestLen];
  CHECK_DIF_OK(dif_kmac_context_restore(&kmac, &context_a, &op_state));
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, &msg_a[test->block_len],
                               kTailLen, NULL));
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &op_state, got_a, kDigestLen,
                                /*processed=*/NULL, /*capacity=*/NULL));
  CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

  // Complete stream B.
  uint32_t got_b[kDigestLen];
  CHECK_DIF_OK(dif_kmac_context_restore(&kmac, &context_b, &op_state));
  CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, &msg_b[test->block_len],
                               kTailLen, NULL));
  CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &op_state, got_b, kDigestLen,
                                /*processed=*/NULL, /*capacity=*/NULL));
  CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

  check_digest(test, "interleaved stream A", got_a, want_a);
  check_digest(test, "interleaved stream B", got_b, want_b);
}

bool test_main(void) {
  static_assert(kDtKmacCount >= 1,
                "This test requires at least one KMAC instance");
  CHECK_DIF_OK(dif_kmac_init_from_dt(kKmacDt, &kmac));

  // Configure KMAC hardware using software entropy. The seed has been randomly
  // chosen and is generated using
  // ./util/design/gen-lfsr-seed.py --width 192 --seed 2034386436 --prefix ""
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  for (size_t i = 0; i < ARRAYSIZE(kSrTests); ++i) {
    const sr_test_t *test = &kSrTests[i];
    CHECK(test->block_len <= kMaxBlockLen, "block length too large");

    LOG_INFO("Testing save and restore in %s mode", test->name);
    test_save_restore(test);
    test_interleaved(test);
  }

  return true;
}
