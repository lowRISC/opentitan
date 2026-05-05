// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'r')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_p384);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, mode);   // Mode of operation.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, msg);    // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, r);      // ECDSA signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, s);      // ECDSA signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, x);      // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, y);      // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, d0_io);  // Private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p384, d1_io);  // Private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p384,
                         k0_io);  // Private secret scalar k (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p384,
                         k1_io);          // Private secret scalar k (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p384, x_r);  // ECDSA verification result.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, ok);   // Status code.

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIGN_CONFIG_K);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_POINTONCRV_CHECK);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_BASE_POINT_MULT);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_ARITH_SHARE_SECRET_KEY);

enum {
  /*
   * Mode is represented by a single word.
   */
  kP384ModeWords = 1,
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
       (kP384MaskedScalarShareWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
  /**
   * Number of extra padding words needed for unmasked scalars.
   */
  kScalarPaddingWords =
      (kOtbnWideWordNumWords - (kP384ScalarWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
  /**
   * Number of extra padding words needed for unmasked coordinates.
   */
  kCoordPaddingWords =
      (kOtbnWideWordNumWords - (kP384CoordWords % kOtbnWideWordNumWords)) %
      kOtbnWideWordNumWords,
  /*
   * The expected instruction counts for constant time functions.
   */
  kModeKeygenInsCnt = 1961351,
  kModeKeygenSideloadInsCnt = 1961244,
  kModeEcdhInsCnt = 1972956,
  kModeEcdhSideloadInsCnt = 1973102,
  kModeEcdsaSignConfigKInsCnt = 1600471,
  kModeEcdsaSignInsCnt = 1600692,
  kModeEcdsaSignSideloadInsCnt = 1600838,
  kModePointOnCurveCheckInsCnt = 357,
  kModePointOnCurveCheckInvld1InsCnt = 348,
  kModePointOnCurveCheckInvld2InsCnt = 355,
  kModePointOnCurveCheckInvldXRangeInsCnt = 40,
  kModePointOnCurveCheckInvldYRangeInsCnt = 48,
  kModeBasePointMultInsCnt = 1961105,
  kModeArithShareSecretKeyInsCnt = 308,
};

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p384_init_otbn(
    uint32_t mode) {
  const otbn_app_t kOtbnAppP384 = OTBN_APP_T_INIT(run_p384);
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));
  const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_p384, mode);
  return otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p384_read_point(
    p384_point_t *point) {
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p384, x);
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p384, y);
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarX, point->x));
  return otbn_dmem_read(kP384CoordWords, kOtbnVarY, point->y);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p384_check_otbn_status(void) {
  uint32_t ok;
  const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p384, ok);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    HARDENED_TRY(otbn_dmem_sec_wipe());
    // COVERAGE (MISSING) We do not cover a negative ECDH check where a bad
    // public key is given.
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p384_masked_scalar_write(
    p384_masked_scalar_t *src, const otbn_addr_t share0_addr,
    const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share1, share1_addr));
  HARDENED_CHECK_EQ(p384_masked_scalar_checksum_check(src), kHardenedBoolTrue);

  // Write trailing 0s so that OTBN's 384-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP384MaskedScalarShareBytes));
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share1_addr + kP384MaskedScalarShareBytes));

  return OTCRYPTO_OK;
}

/**
 * Write a scalar-sized value into DMEM, with padding as needed.
 *
 * @param src Source value.
 * @param addr DMEM address to write.
 */
OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t p384_scalar_write(
    const uint32_t src[kP384ScalarWords], const otbn_addr_t addr) {
  HARDENED_TRY(otbn_dmem_write(kP384ScalarWords, src, addr));

  return otbn_dmem_set(kScalarPaddingWords, 0, addr + kP384ScalarBytes);
}

/**
 * Write a point into the x and y buffers, with padding as needed.
 *
 * @param p Point to write.
 */
OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t set_public_key(
    const p384_point_t *p) {
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p384, x);
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p384, y);
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, p->x, kOtbnVarX));
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, p->y, kOtbnVarY));

  HARDENED_TRY(
      otbn_dmem_set(kCoordPaddingWords, 0, kOtbnVarX + kP384CoordBytes));
  return otbn_dmem_set(kCoordPaddingWords, 0, kOtbnVarY + kP384CoordBytes);
}

OT_NOINLINE OT_WARN_UNUSED_RESULT static status_t set_message_digest(
    const uint32_t digest[kP384ScalarWords], const otbn_addr_t dst) {
  // Set the message digest. We swap all the bytes so that OTBN can interpret
  // the digest as a little-endian integer, which is a more natural fit for the
  // architecture than the big-endian form requested by the specification (FIPS
  // 186-5, section B.2.1).
  uint32_t digest_little_endian[kP384ScalarWords];
  size_t i = 0;
  for (; launder32(i) < kP384ScalarWords; i++) {
    digest_little_endian[i] =
        __builtin_bswap32(digest[kP384ScalarWords - 1 - i]);
  }
  HARDENED_CHECK_EQ(i, kP384ScalarWords);
  return p384_scalar_write(digest_little_endian, dst);
}

uint32_t p384_masked_scalar_checksum(const p384_masked_scalar_t *scalar) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)scalar->share0, kP384CoordBytes);
  return crc32_finish(&ctx);
}

hardened_bool_t p384_masked_scalar_checksum_check(
    const p384_masked_scalar_t *scalar) {
  if (scalar->checksum == launder32(p384_masked_scalar_checksum(scalar))) {
    return kHardenedBoolTrue;
  }
  // COVERAGE (FI CM) We only provide correct encoded scalars, this is to check
  // for faults.
  return kHardenedBoolFalse;
}

uint32_t p384_ecdh_shared_key_checksum(const p384_ecdh_shared_key_t *key) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)key->share0, kP384CoordBytes);
  return crc32_finish(&ctx);
}

hardened_bool_t p384_ecdh_shared_key_checksum_check(
    const p384_ecdh_shared_key_t *key) {
  if (key->checksum == launder32(p384_ecdh_shared_key_checksum(key))) {
    return kHardenedBoolTrue;
  }
  // COVERAGE (FI CM) We only provide correct encoded keys, this is to check for
  // faults.
  return kHardenedBoolFalse;
}

status_t p384_keygen_start(void) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_KEYGEN);
  HARDENED_TRY(p384_init_otbn(mode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_keygen_finalize(p384_masked_scalar_t *private_key,
                              p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeKeygenInsCnt);

  // Read the masked private key from OTBN dmem.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD0,
                              private_key->share0));
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD1,
                              private_key->share1));
  private_key->checksum = p384_masked_scalar_checksum(private_key);

  // Read the public key from OTBN dmem.
  HARDENED_TRY(p384_read_point(public_key));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t p384_sideload_keygen_start(void) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_KEYGEN);
  HARDENED_TRY(p384_init_otbn(mode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_sideload_keygen_finalize(p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeKeygenSideloadInsCnt);

  // Read the public key from OTBN dmem.
  HARDENED_TRY(p384_read_point(public_key));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t p384_ecdsa_sign_start(const uint32_t digest[kP384ScalarWords],
                               p384_masked_scalar_t *private_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_SIGN);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the message digest.
  const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p384, msg);
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_sign_config_k_start(const uint32_t digest[kP384ScalarWords],
                                        p384_masked_scalar_t *private_key,
                                        p384_masked_scalar_t *secret_scalar) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_SIGN_CONFIG_K);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the message digest.
  const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p384, msg);
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Set the secret scalar shares.
  const otbn_addr_t kOtbnVarK0 = OTBN_ADDR_T_INIT(run_p384, k0_io);
  const otbn_addr_t kOtbnVarK1 = OTBN_ADDR_T_INIT(run_p384, k1_io);
  HARDENED_TRY(p384_masked_scalar_write(secret_scalar, kOtbnVarK0, kOtbnVarK1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_sideload_sign_start(
    const uint32_t digest[kP384ScalarWords]) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_SIGN);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the message digest.
  const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p384, msg);
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_sign_finalize(p384_ecdsa_signature_t *result) {
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
  const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p384, r);
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarR, result->r));

  // Read signature S out of OTBN dmem.
  const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p384, s);
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarS, result->s));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t p384_ecdsa_verify_start(const p384_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_VERIFY);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the message digest.
  const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p384, msg);
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Set the signature R.
  const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p384, r);
  HARDENED_TRY(p384_scalar_write(signature->r, kOtbnVarR));

  // Set the signature S.
  const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p384, s);
  HARDENED_TRY(p384_scalar_write(signature->s, kOtbnVarS));

  // Set the public key.
  HARDENED_TRY(set_public_key(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_verify_finalize(const p384_ecdsa_signature_t *signature,
                                    hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(p384_check_otbn_status());

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP384ScalarWords];
  const otbn_addr_t kOtbnVarXr = OTBN_ADDR_T_INIT(run_p384, x_r);
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarXr, x_r));

  *result = hardened_memeq(x_r, signature->r, kP384ScalarWords);

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t p384_ecdh_start(p384_masked_scalar_t *private_key,
                         const p384_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_ECDH);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Set the public key.
  HARDENED_TRY(set_public_key(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdh_finalize(p384_ecdh_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  HARDENED_TRY(p384_check_otbn_status());

  // OTBN returned the status code OK, so check for the expected instr. count.
  uint32_t ins_cnt;
  ins_cnt = otbn_instruction_count_get();
  if (launder32(ins_cnt) == kModeEcdhSideloadInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdhSideloadInsCnt);
  } else {
    HARDENED_CHECK_EQ(ins_cnt, kModeEcdhInsCnt);
  }

  // Read the shares of the key from OTBN dmem (at vars x and y).
  const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p384, x);
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarX, shared_key->share0));
  const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p384, y);
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarY, shared_key->share1));

  shared_key->checksum = p384_ecdh_shared_key_checksum(shared_key);

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t p384_sideload_ecdh_start(const p384_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_ECDH);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the public key.
  HARDENED_TRY(set_public_key(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_point_on_curve_check(const p384_point_t *point,
                                   hardened_bool_t *result) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_POINTONCRV_CHECK);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the point.
  HARDENED_TRY(set_public_key(point));

  // Start the OTBN routine.
  HARDENED_TRY(otbn_execute());

  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  uint32_t ins_cnt = otbn_instruction_count_get();
  if (launder32(ins_cnt) == kModePointOnCurveCheckInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModePointOnCurveCheckInsCnt);
  } else if (launder32(ins_cnt) == kModePointOnCurveCheckInvld1InsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModePointOnCurveCheckInvld1InsCnt);
  } else if (launder32(ins_cnt) == kModePointOnCurveCheckInvldXRangeInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModePointOnCurveCheckInvldXRangeInsCnt);
  } else if (launder32(ins_cnt) == kModePointOnCurveCheckInvldYRangeInsCnt) {
    HARDENED_CHECK_EQ(ins_cnt, kModePointOnCurveCheckInvldYRangeInsCnt);
  } else {
    // COVERAGE (MISSING) We do not cover PointOnCurveCheckInvld2
    HARDENED_CHECK_EQ(ins_cnt, kModePointOnCurveCheckInvld2InsCnt);
  }

  // Read the result of the OTBN operation.
  const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p384, ok);
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, result));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_base_point_mult(p384_masked_scalar_t *private_key,
                              p384_point_t *public_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_BASE_POINT_MULT);
  HARDENED_TRY(p384_init_otbn(mode));

  // Set the private key shares.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  HARDENED_TRY(otbn_execute());

  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  HARDENED_CHECK_EQ(otbn_instruction_count_get(), kModeBasePointMultInsCnt);

  // Read the public key from OTBN dmem.
  HARDENED_TRY(p384_read_point(public_key));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

OT_WARN_UNUSED_RESULT
status_t p384_arith_share_private_key(p384_masked_scalar_t *boolean_private_key,
                                      p384_masked_scalar_t *arith_private_key) {
  uint32_t mode = OTBN_ADDR_T_INIT(run_p384, MODE_ARITH_SHARE_SECRET_KEY);
  HARDENED_TRY(p384_init_otbn(mode));

  // Write the Boolean-shared key to DMEM.
  const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
  const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
  HARDENED_TRY(
      p384_masked_scalar_write(boolean_private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  HARDENED_TRY(otbn_execute());

  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Check if we executed the expected number of OTBN instructions.
  HARDENED_CHECK_EQ(otbn_instruction_count_get(),
                    kModeArithShareSecretKeyInsCnt);

  // Read back the shared private key.
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD0,
                              arith_private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD1,
                              arith_private_key->share1));

  return otbn_dmem_sec_wipe();
}
