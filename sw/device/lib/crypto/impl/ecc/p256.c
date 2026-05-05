// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p256.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/include/integrity.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', 'r')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_p256);  // The OTBN P-256 app.

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, mode);   // Mode of operation.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, msg);    // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, r);      // ECDSA signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, s);      // ECDSA signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x);      // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, y);      // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d0_io);  // Private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d1_io);  // Private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, k0_io);  // Secret scalar k (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, k1_io);  // Secret scalar k (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x_r);    // ECDSA verification result.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, ok);     // Status code.
OTBN_DECLARE_SYMBOL_ADDR(
    run_p256,
    attestation_additional_seed);  // Additional seed for attestation keygen.

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIGN_CONFIG_K);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_POINTONCRV_CHECK);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_BASE_POINT_MULT);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_ARITH_SHARE_SECRET_KEY);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnP256ModeWords = 1,
  /**
   * Number of extra padding words needed for masked scalar shares.
   *
   * Where W is the word size and S is the share size, the padding needed is:
   *   (W - (S % W)) % W
   *
   * The extra outer "% W" ensures that the padding is 0 if (S % W) is 0.
   */
  kMaskedScalarPaddingWords =
      (kOtbnWideWordNumWords -
       (kP256MaskedScalarShareWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
  /*
   * The expected instruction counts for constant time functions.
   */
  kModeKeygenInsCnt = 573922,
  kModeKeygenSideloadInsCnt = 573814,
  kModeEcdhInsCnt = 581607,
  kModeEcdhSideloadInsCnt = 581672,
  kModeEcdsaSignConfigKInsCnt = 607096,
  kModeEcdsaSignInsCnt = 606946,
  kModeEcdsaSignSideloadInsCnt = 607161,
  kModePointOnCurveCheckInsCnt = 224,
  kModeBasePointMultInsCnt = 573756,
  kModeArithShareSecretKeyInsCnt = 147,
};

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_init_otbn(
    uint32_t mode) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  const otbn_app_t kOtbnAppP256 = OTBN_APP_T_INIT(run_p256);
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));
  // Set mode so start() will jump into the requested routine.
  const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_p256, mode);
  return otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_write_point(
    const p256_point_t *point) {
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p256, x);
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p256, y);
  // Set the point x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, point->x, kOtbnVarX));
  // Set the point y coordinate.
  return otbn_dmem_write(kP256CoordWords, point->y, kOtbnVarY);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_read_point(
    p256_point_t *point) {
  // Read the public key from OTBN dmem.
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p256, x);
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p256, y);
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarX, point->x));
  return otbn_dmem_read(kP256CoordWords, kOtbnVarY, point->y);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_write_attestation_seed(
    const otcrypto_const_word32_buf_t *attestation_seed) {
  const otbn_addr_t kOtbnVarBootAttestationAdditionalSeed =
      OTBN_ADDR_T_INIT(run_p256, attestation_additional_seed);
  if (attestation_seed == NULL) {
    // No attestation seed is used.
    return otbn_dmem_set(kDiceAttestationMaxSeedLength, 0,
                         kOtbnVarBootAttestationAdditionalSeed);
  }

  if (launder32(attestation_seed->len) > kDiceAttestationMaxSeedLength) {
    // COVERAGE (MISSING) We do not cover too long attestation seed inputs.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(attestation_seed));

  // Write the attestation seed to the extra variables area.
  HARDENED_TRY(otbn_dmem_write(attestation_seed->len, attestation_seed->data,
                               kOtbnVarBootAttestationAdditionalSeed));
  // Pad the remainder by zeros.
  return otbn_dmem_set(kDiceAttestationMaxSeedLength - attestation_seed->len, 0,
                       kOtbnVarBootAttestationAdditionalSeed +
                           attestation_seed->len * sizeof(uint32_t));
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_check_otbn_status(void) {
  // Read the status code out of DMEM (false if basic checks on the validity of
  // the signature and public key failed).
  uint32_t ok;
  const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p256, ok);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p256_masked_scalar_write(
    p256_masked_scalar_t *src, const otbn_addr_t share0_addr,
    const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share1, share1_addr));
  HARDENED_CHECK_EQ(p256_masked_scalar_checksum_check(src), kHardenedBoolTrue);

  // Write trailing 0s so that OTBN's 256-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP256MaskedScalarShareBytes));
  return otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                       share1_addr + kP256MaskedScalarShareBytes);
}

/**
 * Set the message digest for signature generation or verification.
 *
 * OTBN requires the digest in little-endian form, so this routine flips the
 * bytes.
 *
 * @param digest Digest to set (big-endian).
 * @return OK or error.
 */
OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t set_message_digest(
    const uint32_t digest[kP256ScalarWords]) {
  // Set the message digest. We swap all the bytes so that OTBN can interpret
  // the digest as a little-endian integer, which is a more natural fit for the
  // architecture than the big-endian form requested by the specification (FIPS
  // 186-5, section B.2.1).
  uint32_t digest_little_endian[kP256ScalarWords];
  size_t i = 0;
  for (; launder32(i) < kP256ScalarWords; i++) {
    digest_little_endian[i] =
        __builtin_bswap32(digest[kP256ScalarWords - 1 - i]);
  }
  HARDENED_CHECK_EQ(i, kP256ScalarWords);
  const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p256, msg);
  return otbn_dmem_write(kP256ScalarWords, digest_little_endian, kOtbnVarMsg);
}

uint32_t p256_masked_scalar_checksum(const p256_masked_scalar_t *scalar) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)scalar->share0, kP256CoordBytes);
  return crc32_finish(&ctx);
}

hardened_bool_t p256_masked_scalar_checksum_check(
    const p256_masked_scalar_t *scalar) {
  if (scalar->checksum == launder32(p256_masked_scalar_checksum(scalar))) {
    return kHardenedBoolTrue;
  }
  // COVERAGE (FI CM) We only provide correct encoded scalars, this is to check
  // for faults.
  return kHardenedBoolFalse;
}

uint32_t p256_ecdh_shared_key_checksum(const p256_ecdh_shared_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)key->share0, kP256CoordBytes);
  return crc32_finish(&ctx);
}

hardened_bool_t p256_ecdh_shared_key_checksum_check(
    const p256_ecdh_shared_key_t *key) {
  if (key->checksum == launder32(p256_ecdh_shared_key_checksum(key))) {
    return kHardenedBoolTrue;
  }
  // COVERAGE (FI CM) We only provide correct encoded keys, this is to check for
  // faults.
  return kHardenedBoolFalse;
}

status_t p256_keygen_start(void) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_KEYGEN);
  HARDENED_TRY(p256_init_otbn(mode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_sideload_keygen_start(void) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_KEYGEN);
  HARDENED_TRY(p256_init_otbn(mode));
  HARDENED_TRY(p256_write_attestation_seed(NULL));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_sideload_attestation_keygen_start(
    const otcrypto_const_word32_buf_t *attestation_seed) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_KEYGEN);
  HARDENED_TRY(p256_init_otbn(mode));
  HARDENED_TRY(p256_write_attestation_seed(attestation_seed));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_keygen_finalize(p256_masked_scalar_t *private_key,
                              p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeKeygenInsCnt);

  // Read the masked private key from OTBN dmem.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD0,
                              private_key->share0));
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD1,
                              private_key->share1));
  private_key->checksum = p256_masked_scalar_checksum(private_key);

  // Read the public key from OTBN dmem.
  HARDENED_TRY(p256_read_point(public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_sideload_keygen_finalize(p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeKeygenSideloadInsCnt);

  // Read the public key from OTBN dmem.
  HARDENED_TRY(p256_read_point(public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_ecdsa_sign_start(const uint32_t digest[kP256ScalarWords],
                               p256_masked_scalar_t *private_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIGN);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_sign_config_k_start(const uint32_t digest[kP256ScalarWords],
                                        p256_masked_scalar_t *private_key,
                                        p256_masked_scalar_t *secret_scalar) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIGN_CONFIG_K);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Set the secret scalar shares.
  const otbn_addr_t kOtbnVarK0 = OTBN_ADDR_T_INIT(run_p256, k0_io);
  const otbn_addr_t kOtbnVarK1 = OTBN_ADDR_T_INIT(run_p256, k1_io);
  HARDENED_TRY(p256_masked_scalar_write(secret_scalar, kOtbnVarK0, kOtbnVarK1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_sideload_sign_start(
    const uint32_t digest[kP256ScalarWords]) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_SIGN);
  HARDENED_TRY(p256_init_otbn(mode));
  HARDENED_TRY(p256_write_attestation_seed(NULL));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_sideload_attestation_sign_start(
    const uint32_t digest[kP256ScalarWords],
    const otcrypto_const_word32_buf_t *attestation_seed) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_SIGN);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  HARDENED_TRY(p256_write_attestation_seed(attestation_seed));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_sign_finalize(p256_ecdsa_signature_t *result) {
  uint32_t ins_cnt;
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  ins_cnt = otbn_instruction_count_get();
  if (launder32(ins_cnt) == kModeEcdsaSignSideloadInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdsaSignSideloadInsCnt);
  } else if (launder32(ins_cnt) == kModeEcdsaSignConfigKInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdsaSignConfigKInsCnt);
  } else {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdsaSignInsCnt);
  }

  // Read signature R out of OTBN dmem.
  const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p256, r);
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarR, result->r));

  // Read signature S out of OTBN dmem.
  const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p256, s);
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarS, result->s));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_ecdsa_verify_start(const p256_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP256ScalarWords],
                                 const p256_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_VERIFY);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the signature R.
  const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p256, r);
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->r, kOtbnVarR));

  // Set the signature S.
  const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p256, s);
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->s, kOtbnVarS));

  HARDENED_TRY(p256_write_point(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_verify_finalize(const p256_ecdsa_signature_t *signature,
                                    hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(p256_check_otbn_status());

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP256ScalarWords];
  const otbn_addr_t kOtbnVarXr = OTBN_ADDR_T_INIT(run_p256, x_r);
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarXr, x_r));

  *result = hardened_memeq(x_r, signature->r, kP256ScalarWords);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_ecdh_start(p256_masked_scalar_t *private_key,
                         const p256_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_ECDH);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  HARDENED_TRY(p256_write_point(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdh_finalize(p256_ecdh_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(p256_check_otbn_status());

  // OTBN returned the status code OK, so check for the expected instr. count.
  uint32_t ins_cnt;
  ins_cnt = otbn_instruction_count_get();
  if (launder32(ins_cnt) == kModeEcdhSideloadInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdhSideloadInsCnt);
  } else {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdhInsCnt);
  }

  // Read the shares of the key from OTBN dmem (at vars x and y).
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p256, x);
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarX, shared_key->share0));
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p256, y);
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarY, shared_key->share1));

  shared_key->checksum = p256_ecdh_shared_key_checksum(shared_key);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_sideload_ecdh_start(const p256_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_ECDH);
  HARDENED_TRY(p256_init_otbn(mode));
  HARDENED_TRY(p256_write_point(public_key));
  HARDENED_TRY(p256_write_attestation_seed(NULL));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_point_on_curve_check(const p256_point_t *point,
                                   hardened_bool_t *result) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_POINTONCRV_CHECK);
  HARDENED_TRY(p256_init_otbn(mode));
  HARDENED_TRY(p256_write_point(point));

  // Start the OTBN routine.
  HARDENED_TRY(otbn_execute());

  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModePointOnCurveCheckInsCnt);

  // Read the result of the OTBN operation.
  const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p256, ok);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, result));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_base_point_mult(p256_masked_scalar_t *private_key,
                              p256_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_BASE_POINT_MULT);
  HARDENED_TRY(p256_init_otbn(mode));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  HARDENED_TRY(otbn_execute());

  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeBasePointMultInsCnt);

  HARDENED_TRY(p256_read_point(public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

OT_WARN_UNUSED_RESULT
status_t p256_arith_share_private_key(p256_masked_scalar_t *boolean_private_key,
                                      p256_masked_scalar_t *arith_private_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p256, MODE_ARITH_SHARE_SECRET_KEY);
  HARDENED_TRY(p256_init_otbn(mode));

  // Write the Boolean-shared key to DMEM.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
  HARDENED_TRY(
      p256_masked_scalar_write(boolean_private_key, kOtbnVarD0, kOtbnVarD1));

  /* // Start the OTBN routine. */
  HARDENED_TRY(otbn_execute());

  /* // Spin here waiting for OTBN to complete. */
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  HARDENED_CHECK_EQ(otbn_instruction_count_get(),
                    kModeArithShareSecretKeyInsCnt);

  // Read back the shared private key.
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD0,
                              arith_private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD1,
                              arith_private_key->share1));

  return otbn_dmem_sec_wipe();
}
