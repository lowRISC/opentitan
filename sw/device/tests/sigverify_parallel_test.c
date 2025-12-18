// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/rv_timer.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_ecdsa_p256.h"
#include "sw/device/silicon_creator/lib/ownership/keys/fake/app_prod_spx.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/tests/sigverify_parallel_data.h"
#include "sw/device/tests/sigverify_parallel_digest.h"
#include "sw/device/tests/sigverify_parallel_ecdsa.h"
#include "sw/device/tests/sigverify_parallel_spx.h"

OTTF_DEFINE_TEST_CONFIG();

// This is a near-copy of the SPX verify function from the ROM_EXT.
// Most of the hardening has been remove to simplify the function for use in
// testing.
static rom_error_t do_spx_verify(const sigverify_spx_signature_t *signature,
                                 const sigverify_spx_key_t *key,
                                 uint32_t key_alg, const void *msg_prefix_1,
                                 size_t msg_prefix_1_len,
                                 const void *msg_prefix_2,
                                 size_t msg_prefix_2_len, const void *msg,
                                 size_t msg_len, hmac_digest_t digest) {
  key_alg &= ~(uint32_t)kOwnershipKeyAlgCategoryMask;
  key_alg |= (uint32_t)kOwnershipKeyAlgCategorySpx;

  sigverify_spx_root_t actual_root;
  sigverify_spx_root_t expected_root;
  spx_public_key_root(key->data, expected_root.data);

  switch (key_alg) {
    case kOwnershipKeyAlgSpxPure:
      HARDENED_RETURN_IF_ERROR(spx_verify(
          signature->data, kSpxVerifyPureDomainSep, kSpxVerifyPureDomainSepSize,
          msg_prefix_1, msg_prefix_1_len, msg_prefix_2, msg_prefix_2_len, msg,
          msg_len, key->data, actual_root.data));
      break;

    case kOwnershipKeyAlgSpxPrehash:
      util_reverse_bytes(digest.digest, sizeof(digest.digest));
      HARDENED_RETURN_IF_ERROR(
          spx_verify(signature->data, kSpxVerifyPrehashDomainSep,
                     kSpxVerifyPrehashDomainSepSize,
                     /*msg_prefix_2=*/NULL, /*msg_prefix_2_len=*/0,
                     /*msg_prefix_3=*/NULL, /*msg_prefix_3_len=*/0,
                     (unsigned char *)digest.digest, sizeof(digest.digest),
                     key->data, actual_root.data));
      break;
    default:
      return kErrorSigverifyBadSpxConfig;
  }
  if (memcmp(expected_root.data, actual_root.data,
             sizeof(expected_root.data))) {
    return kErrorSigverifyBadSpxSignature;
  }
  return kErrorOk;
}

typedef struct stats {
  uint32_t iterations;
  uint32_t hashing;
  uint32_t ecdsa_setup;
  uint32_t ecdsa_finish;
  uint32_t spx_verify;
  uint32_t total;
} stats_t;

static rom_error_t parallel_verify(const void *data, size_t len,
                                   const ecdsa_p256_signature_t *ecdsa_sig,
                                   const ecdsa_p256_public_key_t *ecdsa_key,
                                   const sigverify_spx_signature_t *spx_sig,
                                   const sigverify_spx_key_t *spx_key,
                                   uint32_t spx_alg, stats_t *stats) {
  uint32_t t0 = rv_timer_get();
  hmac_digest_t act_digest;
  hmac_sha256(data, len, &act_digest);

  uint32_t t1 = rv_timer_get();
  stats->hashing += t1 - t0;
  // Hybrid signatures check both ECDSA and SPX+ signatures.
  // Start the ECDSA verify.
  HARDENED_RETURN_IF_ERROR(
      sigverify_ecdsa_p256_start(ecdsa_sig, ecdsa_key, &act_digest));
  uint32_t t2 = rv_timer_get();
  stats->ecdsa_setup += t2 - t1;

  // While ECDSA verify is running in OTBN, compute the SPX verify on Ibex.
  rom_error_t spx = do_spx_verify(spx_sig, spx_key, spx_alg, NULL, 0, NULL, 0,
                                  data, len, act_digest);
  HARDENED_RETURN_IF_ERROR(spx);
  uint32_t t3 = rv_timer_get();
  stats->spx_verify += t3 - t2;

  // ECDSA should be finished.  Poll for completeion and get the result.
  uint32_t flash_exec = 0;
  rom_error_t ecdsa = sigverify_ecdsa_p256_finish(ecdsa_sig, &flash_exec);
  HARDENED_RETURN_IF_ERROR(ecdsa);
  uint32_t t4 = rv_timer_get();
  stats->ecdsa_finish += t4 - t3;
  stats->total += t4 - t0;
  stats->iterations += 1;

  // Both values should be kErrorOk.  Mix them and return the result.
  return (rom_error_t)((ecdsa + spx) >> 1);
}

static status_t do_parallel_verify(void) {
  const ecdsa_p256_public_key_t ecdsa_key = APP_PROD_ECDSA_P256;
  const sigverify_spx_key_t spx_key = APP_PROD_SPX;

  stats_t stats = {0};
  for (size_t i = 0; i < 100; ++i) {
    TRY(parallel_verify(
        sigverify_parallel_data, sizeof(sigverify_parallel_data),
        (const ecdsa_p256_signature_t *)sigverify_parallel_ecdsa, &ecdsa_key,
        (const sigverify_spx_signature_t *)sigverify_parallel_spx, &spx_key,
        kOwnershipKeyAlgSpxPrehash, &stats));
  }
  dbg_printf("---\r\n");
  dbg_printf("iterations: %u\r\n", stats.iterations);
  dbg_printf("hashing: %uus\r\n", stats.hashing);
  dbg_printf("ecdsa_setup: %uus\r\n", stats.ecdsa_setup);
  dbg_printf("ecdsa_finish: %uus\r\n", stats.ecdsa_finish);
  dbg_printf("spx_verify: %uus\r\n", stats.spx_verify);
  dbg_printf("total: %uus\r\n", stats.total);
  return OK_STATUS();
}

#ifndef STRESS_TEST
// By default, this test will run a single batch of 100 parallel verify and
// report statistics.
static status_t parallel_verify_test(void) { return do_parallel_verify(); }
#else
// If you run this test with `--copt=-DSTRESS_TEST`, the test will loop
// forever running parallel verify continuously.
static status_t parallel_verify_test(void) {
  for (;;) {
    TRY(do_parallel_verify());
  }
  return OK_STATUS();
}
#endif

bool test_main(void) {
  rv_timer_init();
  return status_ok(parallel_verify_test());
}
