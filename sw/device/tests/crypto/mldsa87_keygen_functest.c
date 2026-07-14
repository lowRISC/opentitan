// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/crypto/mldsa87_keygen_testvectors.h"

/**
 * Execute a ML-DSA-87 key generation.
 */
static status_t run_mldsa87_keygen(const mldsa87_keygen_testvector_t *vector) {
  otcrypto_blinded_key_t xi = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMldsa87,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = 64,
      .keyblob = (unsigned int *)vector->xi,
  };
  xi.checksum = otcrypto_integrity_blinded_checksum(&xi);

  uint32_t pk_data[kOtcryptoMldsa87PkWords];
  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMldsa87,
      .key_length = kOtcryptoMldsa87PkBytes,
      .key = pk_data,
  };

  uint32_t sk_data[kOtcryptoMldsa87SkWords];
  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMldsa87,
              .key_length = kOtcryptoMldsa87SkBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoMldsa87SkBytes,
      .keyblob = sk_data,
  };

  // Call directly into the internal deterministic key generation function.
  CHECK_STATUS_OK(mldsa87_det_keygen_internal_start(&xi));
  CHECK_STATUS_OK(mldsa87_keygen_internal_finalize(&pk, &sk));

  // Compare the public key.
  CHECK_ARRAYS_EQ(pk_data, vector->pk, kOtcryptoMldsa87PkWords);

  /*
   * Reassemble the unmasked secret key from the generated masked key before
   * the comparison.
   */

  uint32_t sk_clear[1224];
  // RHO (32 bytes)
  memcpy(sk_clear, sk_data, 32);
  // K (32 bytes, masked)
  for (size_t i = 0; i < 8; i++)
    sk_clear[8 + i] = sk_data[8 + i] ^ sk_data[16 + i];
  // TR (64 bytes)
  memcpy(sk_clear + 16, sk_data + 24, 64);
  // S1 (672 bytes, masked)
  for (size_t i = 0; i < 168; i++)
    sk_clear[32 + i] = sk_data[40 + i] ^ sk_data[208 + i];
  // S2 (768 bytes, masked)
  for (size_t i = 0; i < 192; i++)
    sk_clear[200 + i] = sk_data[376 + i] ^ sk_data[568 + i];
  // T0 (3328 bytes)
  memcpy(sk_clear + 392, sk_data + 760, 3328);

  CHECK_ARRAYS_EQ(sk_clear, vector->sk, 1224);

  return OTCRYPTO_OK;
}

/**
 * Pure hashing mode.
 */
static status_t mldsa87_keygen_test(void) {
  return run_mldsa87_keygen(&mldsa87_keygen_testvectors[0]);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, mldsa87_keygen_test);

  return status_ok(result);
}
