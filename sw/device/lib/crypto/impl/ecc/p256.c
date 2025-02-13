// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p256.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', 'r')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_p256);  // The OTBN P-256 app.
static const otbn_app_t kOtbnAppP256 = OTBN_APP_T_INIT(run_p256);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, mode);   // Mode of operation.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, msg);    // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, r);      // ECDSA signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, s);      // ECDSA signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x);      // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, y);      // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d0_io);  // Private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, d1_io);  // Private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p256, x_r);    // ECDSA verification result.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, ok);     // Status code.

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_p256, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p256, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p256, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p256, s);
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p256, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p256, y);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p256, d0_io);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p256, d1_io);
static const otbn_addr_t kOtbnVarXr = OTBN_ADDR_T_INIT(run_p256, x_r);
static const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p256, ok);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p256, MODE_SIDELOAD_ECDH);
static const uint32_t kOtbnP256ModeKeygen =
    OTBN_ADDR_T_INIT(run_p256, MODE_KEYGEN);
static const uint32_t kOtbnP256ModeSign = OTBN_ADDR_T_INIT(run_p256, MODE_SIGN);
static const uint32_t kOtbnP256ModeVerify =
    OTBN_ADDR_T_INIT(run_p256, MODE_VERIFY);
static const uint32_t kOtbnP256ModeEcdh = OTBN_ADDR_T_INIT(run_p256, MODE_ECDH);
static const uint32_t kOtbnP256ModeSideloadKeygen =
    OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_KEYGEN);
static const uint32_t kOtbnP256ModeSideloadSign =
    OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_SIGN);
static const uint32_t kOtbnP256ModeSideloadEcdh =
    OTBN_ADDR_T_INIT(run_p256, MODE_SIDELOAD_ECDH);

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
};

static status_t p256_masked_scalar_write(const p256_masked_scalar_t *src,
                                         const otbn_addr_t share0_addr,
                                         const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP256MaskedScalarShareWords, src->share1, share1_addr));

  // Write trailing 0s so that OTBN's 256-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP256MaskedScalarShareBytes));
  return otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                       share1_addr + kP256MaskedScalarShareBytes);
}

status_t p256_keygen_start(void) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into keygen.
  uint32_t mode = kOtbnP256ModeKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_sideload_keygen_start(void) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into sideload-keygen.
  uint32_t mode = kOtbnP256ModeSideloadKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_keygen_finalize(p256_masked_scalar_t *private_key,
                              p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarY, public_key->y));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_sideload_keygen_finalize(p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarY, public_key->y));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
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
static status_t set_message_digest(const uint32_t digest[kP256ScalarWords]) {
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
  return otbn_dmem_write(kP256ScalarWords, digest_little_endian, kOtbnVarMsg);
}

status_t p256_ecdsa_sign_start(const uint32_t digest[kP256ScalarWords],
                               const p256_masked_scalar_t *private_key) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into signing.
  uint32_t mode = kOtbnP256ModeSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the private key shares.
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_sideload_sign_start(
    const uint32_t digest[kP256ScalarWords]) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kOtbnP256ModeSideloadSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_sign_finalize(p256_ecdsa_signature_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read signature R out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarR, result->r));

  // Read signature S out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarS, result->s));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_ecdsa_verify_start(const p256_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP256ScalarWords],
                                 const p256_point_t *public_key) {
  // Load the P-256 app and set up data pointers
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into verifying.
  uint32_t mode = kOtbnP256ModeVerify;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the signature R.
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->r, kOtbnVarR));

  // Set the signature S.
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->s, kOtbnVarS));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->x, kOtbnVarX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->y, kOtbnVarY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdsa_verify_finalize(const p256_ecdsa_signature_t *signature,
                                    hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the status code out of DMEM (false if basic checks on the validity of
  // the signature and public key failed).
  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP256ScalarWords];
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarXr, x_r));

  *result = hardened_memeq(x_r, signature->r, kP256ScalarWords);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_ecdh_start(const p256_masked_scalar_t *private_key,
                         const p256_point_t *public_key) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into shared-key generation.
  uint32_t mode = kOtbnP256ModeEcdh;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Set the private key shares.
  HARDENED_TRY(p256_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->x, kOtbnVarX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->y, kOtbnVarY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p256_ecdh_finalize(p256_ecdh_shared_key_t *shared_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the code indicating if the public key is valid.
  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read the shares of the key from OTBN dmem (at vars x and y).
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarX, shared_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarY, shared_key->share1));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p256_sideload_ecdh_start(const p256_point_t *public_key) {
  // Load the P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP256));

  // Set mode so start() will jump into shared-key generation.
  uint32_t mode = kOtbnP256ModeSideloadEcdh;
  HARDENED_TRY(otbn_dmem_write(kOtbnP256ModeWords, &mode, kOtbnVarMode));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->x, kOtbnVarX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->y, kOtbnVarY));

  // Start the OTBN routine.
  return otbn_execute();
}
