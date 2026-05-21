// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KATS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KATS_H_

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

typedef enum {
  kTestHashSha256Bit = 0,
  kTestHmacSha256Bit,
  kTestHashSha512Bit,
  kTestHmacSha512Bit,
  kTestDrgbBit,
  kTestP256BasePointMulBit,
  kTestP256PointOnCurveBit,
  kTestP256SignBit,
  kTestP256VerifyBit,
  kTestRsa2048VerifyBit,
  kTestP384SignBit,
  kTestP384VerifyBit,
  kTestP384BasePointMulBit,
  kTestP384PointOnCurveBit,
  kTestAesGcm256EncryptBit,
  kTestAesEcb256DecryptBit,
  kTestRsa4096VerifyBit,
  kTestRsa4096SignBit,
  kTestShake256Bit,
  kTestKmac256Bit,
  // Last entry used for mask calculation
  kTestLastBit,
} otcrypto_kat_bits_t;

#define _FLAG(flag) (1UL << kTest##flag##Bit)

/**
 * Define bit flags for Known-Answer Tests.
 */
#define OTCRYPTO_KAT_HASH_SHA256 _FLAG(HashSha256)
#define OTCRYPTO_KAT_HMAC_SHA256 _FLAG(HmacSha256)
#define OTCRYPTO_KAT_HASH_SHA512 _FLAG(HashSha512)
#define OTCRYPTO_KAT_HMAC_SHA512 _FLAG(HmacSha512)
#define OTCRYPTO_KAT_DRBG _FLAG(Drgb)
#define OTCRYPTO_KAT_P256_BASE_POINT_MUL _FLAG(P256BasePointMul)
#define OTCRYPTO_KAT_P256_POINT_ON_CURVE _FLAG(P256PointOnCurve)
#define OTCRYPTO_KAT_P256_SIGN _FLAG(P256Sign)
#define OTCRYPTO_KAT_P256_VERIFY _FLAG(P256Verify)
#define OTCRYPTO_KAT_RSA2048_VERIFY _FLAG(Rsa2048Verify)
#define OTCRYPTO_KAT_RSA4096_VERIFY _FLAG(Rsa4096Verify)
#define OTCRYPTO_KAT_RSA4096_SIGN _FLAG(Rsa4096Sign)
#define OTCRYPTO_KAT_P384_BASE_POINT_MUL _FLAG(P384BasePointMul)
#define OTCRYPTO_KAT_P384_POINT_ON_CURVE _FLAG(P384PointOnCurve)
#define OTCRYPTO_KAT_P384_SIGN _FLAG(P384Sign)
#define OTCRYPTO_KAT_P384_VERIFY _FLAG(P384Verify)
#define OTCRYPTO_KAT_AES_GCM_256_ENCRYPT _FLAG(AesGcm256Encrypt)
#define OTCRYPTO_KAT_AES_ECB_256_DECRYPT _FLAG(AesEcb256Decrypt)
#define OTCRYPTO_KAT_SHAKE_256 _FLAG(Shake256)
#define OTCRYPTO_KAT_KMAC_256 _FLAG(Kmac256)

typedef struct {
  uint64_t flags;
} otcrypto_kat_id_t;

#define OTCRYPTO_KAT_FLAGS(_flags) ((otcrypto_kat_id_t){.flags = _flags})

#define OTCRYPTO_KAT_ALL_TESTS OTCRYPTO_KAT_FLAGS(((1UL << kTestLastBit) - 1))

/**
 * @brief Run Known-Answer Test (KAT) for the requested algorithms
 *
 * @param tests_to_run bit mask with tests to run
 * @return OK if the requested KATs passed.
 */
otcrypto_status_t run_kats(otcrypto_kat_id_t tests_to_run);

/**
 * @brief Ensures the specified Known-Answer Test (KAT) is executed exactly
 * once.
 *
 * This function provides stateful, lazy evaluation of KATs depending on the
 * build configuration:
 *
 * - **FIPS Build (`KAT_CHECK_ENABLE` defined):** It checks a tethered state
 *   variable (provided by the host firmware) to verify if the KAT corresponding
 *   to `kat_bit` has already run. If not, it executes the KAT and securely
 *   updates the state. Subsequent calls for the same KAT will bypass execution.
 * - **Standard Build (`KAT_CHECK_ENABLE` undefined):** The function evaluates
 *   to a static inline no-op. It returns `OTCRYPTO_OK` immediately to avoid
 *   unnecessary execution and linker dependencies.
 *
 * @param kat_bit The specific KAT to execute (e.g.,
 * `kTestAesEcb256DecryptBit`).
 * @return Result of the operation. Returns `OTCRYPTO_OK` on success, if the
 *         KAT already passed, or if lazy evaluation is disabled. Returns
 *         `OTCRYPTO_FATAL_ERR` if the KAT fails or the state pointer is
 * missing.
 */
#ifndef KAT_CHECK_ENABLE

// STANDARD BUILD: Lazy KAT evaluation is disabled.
// Defined as static inline so the compiler embeds the OK status directly
// into aes.c, avoiding any linker dependency on kats.o.
static inline otcrypto_status_t otcrypto_stateful_kat(
    otcrypto_kat_bits_t kat_bit) {
  return OTCRYPTO_OK;
}

#else

// FIPS BUILD: Evaluates lazily using host-tethered state.
// Implementation lives in kats.c
otcrypto_status_t otcrypto_stateful_kat(otcrypto_kat_bits_t kat_bit);

#endif  // KAT_CHECK_ENABLE

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KATS_H_
