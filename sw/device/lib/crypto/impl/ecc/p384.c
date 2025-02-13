// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '3', 'r')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(run_p384);
static const otbn_app_t kOtbnAppP384 = OTBN_APP_T_INIT(run_p384);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, mode);   // Mode of operation.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, msg);    // ECDSA message digest.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, r);      // ECDSA signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, s);      // ECDSA signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, x);      // Public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, y);      // Public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, d0_io);  // Private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(run_p384, d1_io);  // Private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(run_p384, x_r);    // ECDSA verification result.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, ok);     // Status code.

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_p384, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(run_p384, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(run_p384, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(run_p384, s);
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(run_p384, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(run_p384, y);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(run_p384, d0_io);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(run_p384, d1_io);
static const otbn_addr_t kOtbnVarXr = OTBN_ADDR_T_INIT(run_p384, x_r);
static const otbn_addr_t kOtbnVarOk = OTBN_ADDR_T_INIT(run_p384, ok);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_ECDH);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(run_p384, MODE_SIDELOAD_ECDH);
static const uint32_t kP384ModeKeygen = OTBN_ADDR_T_INIT(run_p384, MODE_KEYGEN);
static const uint32_t kP384ModeSign = OTBN_ADDR_T_INIT(run_p384, MODE_SIGN);
static const uint32_t kP384ModeVerify = OTBN_ADDR_T_INIT(run_p384, MODE_VERIFY);
static const uint32_t kP384ModeEcdh = OTBN_ADDR_T_INIT(run_p384, MODE_ECDH);
static const uint32_t kP384ModeSideloadKeygen =
    OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_KEYGEN);
static const uint32_t kP384ModeSideloadSign =
    OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_SIGN);
static const uint32_t kP384ModeSideloadEcdh =
    OTBN_ADDR_T_INIT(run_p384, MODE_SIDELOAD_ECDH);

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
};

static status_t p384_masked_scalar_write(const p384_masked_scalar_t *src,
                                         const otbn_addr_t share0_addr,
                                         const otbn_addr_t share1_addr) {
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share0, share0_addr));
  HARDENED_TRY(
      otbn_dmem_write(kP384MaskedScalarShareWords, src->share1, share1_addr));

  // Write trailing 0s so that OTBN's 384-bit read of the second share does not
  // cause an error.
  HARDENED_TRY(otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                             share0_addr + kP384MaskedScalarShareBytes));
  return otbn_dmem_set(kMaskedScalarPaddingWords, 0,
                       share1_addr + kP384MaskedScalarShareBytes);
}

/**
 * Write a scalar-sized value into DMEM, with padding as needed.
 *
 * @param src Source value.
 * @param addr DMEM address to write.
 */
static status_t p384_scalar_write(const uint32_t src[kP384ScalarWords],
                                  const otbn_addr_t addr) {
  HARDENED_TRY(otbn_dmem_write(kP384ScalarWords, src, addr));

  return otbn_dmem_set(kScalarPaddingWords, 0, addr + kP384ScalarBytes);
}

/**
 * Write a point into the x and y buffers, with padding as needed.
 *
 * @param p Point to write.
 */
static status_t set_public_key(const p384_point_t *p) {
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, p->x, kOtbnVarX));
  HARDENED_TRY(otbn_dmem_write(kP384CoordWords, p->y, kOtbnVarY));

  HARDENED_TRY(
      otbn_dmem_set(kCoordPaddingWords, 0, kOtbnVarX + kP384CoordBytes));
  return otbn_dmem_set(kCoordPaddingWords, 0, kOtbnVarY + kP384CoordBytes);
}

static status_t set_message_digest(const uint32_t digest[kP384ScalarWords],
                                   const otbn_addr_t dst) {
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

status_t p384_keygen_start(void) {
  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into keygen.
  uint32_t mode = kP384ModeKeygen;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_keygen_finalize(p384_masked_scalar_t *private_key,
                              p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP384MaskedScalarShareWords, kOtbnVarD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarY, public_key->y));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_sideload_keygen_start(void) {
  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into keygen.
  uint32_t mode = kP384ModeSideloadKeygen;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_sideload_keygen_finalize(p384_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarY, public_key->y));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_ecdsa_sign_start(const uint32_t digest[kP384ScalarWords],
                               const p384_masked_scalar_t *private_key) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kP384ModeSign;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Set the private key shares.
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_sideload_sign_start(
    const uint32_t digest[kP384ScalarWords]) {
  // Load the ECDSA/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kP384ModeSideloadSign;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdsa_sign_finalize(p384_ecdsa_signature_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read signature R out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarR, result->r));

  // Read signature S out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarS, result->s));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_ecdsa_verify_start(const p384_ecdsa_signature_t *signature,
                                 const uint32_t digest[kP384ScalarWords],
                                 const p384_point_t *public_key) {
  // Load the ECDSA/P-384 app
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into ECDSA verify.
  uint32_t mode = kP384ModeVerify;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest, kOtbnVarMsg));

  // Set the signature R.
  HARDENED_TRY(p384_scalar_write(signature->r, kOtbnVarR));

  // Set the signature S.
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

  // Read the status code out of DMEM (false if basic checks on the validity of
  // the signature and public key failed).
  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP384ScalarWords];
  HARDENED_TRY(otbn_dmem_read(kP384ScalarWords, kOtbnVarXr, x_r));

  *result = hardened_memeq(x_r, signature->r, kP384ScalarWords);

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_ecdh_start(const p384_masked_scalar_t *private_key,
                         const p384_point_t *public_key) {
  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into shared-key generation.
  uint32_t mode = kP384ModeEcdh;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Set the private key shares.
  HARDENED_TRY(p384_masked_scalar_write(private_key, kOtbnVarD0, kOtbnVarD1));

  // Set the public key.
  HARDENED_TRY(set_public_key(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t p384_ecdh_finalize(p384_ecdh_shared_key_t *shared_key) {
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

  // Read the shares of the key from OTBN dmem (at vars x and y).
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarX, shared_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP384CoordWords, kOtbnVarY, shared_key->share1));

  // Wipe DMEM.
  return otbn_dmem_sec_wipe();
}

status_t p384_sideload_ecdh_start(const p384_point_t *public_key) {
  // Load the ECDH/P-384 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppP384));

  // Set mode so start() will jump into shared-key generation.
  uint32_t mode = kP384ModeSideloadEcdh;
  HARDENED_TRY(otbn_dmem_write(kP384ModeWords, &mode, kOtbnVarMode));

  // Set the public key.
  HARDENED_TRY(set_public_key(public_key));

  // Start the OTBN routine.
  return otbn_execute();
}
