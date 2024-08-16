// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdsa_p256.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('p', '2', 's')

// Declare the OTBN app.
OTBN_DECLARE_APP_SYMBOLS(p256_ecdsa);  // The OTBN ECDSA/P-256 app.
static const otbn_app_t kOtbnAppEcdsa = OTBN_APP_T_INIT(p256_ecdsa);

// Declare offsets for input and output buffers.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, mode);  // ECDSA mode (sign or verify).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, msg);   // Message digest.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, r);     // The signature scalar R.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, s);     // The signature scalar S.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x);     // The public key x-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, y);     // The public key y-coordinate.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa,
                         d0);  // The private key scalar d (share 0).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa,
                         d1);  // The private key scalar d (share 1).
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, x_r);  // Verification result.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, ok);   // Status code.

static const otbn_addr_t kOtbnVarEcdsaMode = OTBN_ADDR_T_INIT(p256_ecdsa, mode);
static const otbn_addr_t kOtbnVarEcdsaMsg = OTBN_ADDR_T_INIT(p256_ecdsa, msg);
static const otbn_addr_t kOtbnVarEcdsaR = OTBN_ADDR_T_INIT(p256_ecdsa, r);
static const otbn_addr_t kOtbnVarEcdsaS = OTBN_ADDR_T_INIT(p256_ecdsa, s);
static const otbn_addr_t kOtbnVarEcdsaX = OTBN_ADDR_T_INIT(p256_ecdsa, x);
static const otbn_addr_t kOtbnVarEcdsaY = OTBN_ADDR_T_INIT(p256_ecdsa, y);
static const otbn_addr_t kOtbnVarEcdsaD0 = OTBN_ADDR_T_INIT(p256_ecdsa, d0);
static const otbn_addr_t kOtbnVarEcdsaD1 = OTBN_ADDR_T_INIT(p256_ecdsa, d1);
static const otbn_addr_t kOtbnVarEcdsaXr = OTBN_ADDR_T_INIT(p256_ecdsa, x_r);
static const otbn_addr_t kOtbnVarEcdsaOk = OTBN_ADDR_T_INIT(p256_ecdsa, ok);

// Declare mode constants.
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, MODE_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, MODE_SIGN);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, MODE_VERIFY);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, MODE_SIDELOAD_KEYGEN);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa, MODE_SIDELOAD_SIGN);
static const uint32_t kOtbnEcdsaModeKeygen =
    OTBN_ADDR_T_INIT(p256_ecdsa, MODE_KEYGEN);
static const uint32_t kOtbnEcdsaModeSign =
    OTBN_ADDR_T_INIT(p256_ecdsa, MODE_SIGN);
static const uint32_t kOtbnEcdsaModeVerify =
    OTBN_ADDR_T_INIT(p256_ecdsa, MODE_VERIFY);
static const uint32_t kOtbnEcdsaModeSideloadKeygen =
    OTBN_ADDR_T_INIT(p256_ecdsa, MODE_SIDELOAD_KEYGEN);
static const uint32_t kOtbnEcdsaModeSideloadSign =
    OTBN_ADDR_T_INIT(p256_ecdsa, MODE_SIDELOAD_SIGN);

enum {
  /*
   * Mode is represented by a single word.
   */
  kOtbnEcdsaModeWords = 1,
};

status_t ecdsa_p256_keygen_start(void) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsa));

  // Set mode so start() will jump into keygen.
  uint32_t mode = kOtbnEcdsaModeKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p256_sideload_keygen_start(void) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsa));

  // Set mode so start() will jump into sideload-keygen.
  uint32_t mode = kOtbnEcdsaModeSideloadKeygen;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p256_keygen_finalize(p256_masked_scalar_t *private_key,
                                    p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the masked private key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarEcdsaD0,
                              private_key->share0));
  HARDENED_TRY(otbn_dmem_read(kP256MaskedScalarShareWords, kOtbnVarEcdsaD1,
                              private_key->share1));

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdsaX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdsaY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdsa_p256_sideload_keygen_finalize(p256_point_t *public_key) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public key from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdsaX, public_key->x));
  HARDENED_TRY(otbn_dmem_read(kP256CoordWords, kOtbnVarEcdsaY, public_key->y));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
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
  return otbn_dmem_write(kP256ScalarWords, digest_little_endian,
                         kOtbnVarEcdsaMsg);
}

status_t ecdsa_p256_sign_start(const uint32_t digest[kP256ScalarWords],
                               const p256_masked_scalar_t *private_key) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsa));

  // Set mode so start() will jump into signing.
  uint32_t mode = kOtbnEcdsaModeSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the private key shares.
  HARDENED_TRY(
      p256_masked_scalar_write(private_key, kOtbnVarEcdsaD0, kOtbnVarEcdsaD1));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p256_sideload_sign_start(
    const uint32_t digest[kP256ScalarWords]) {
  // Load the ECDSA/P-256 app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsa));

  // Set mode so start() will jump into sideloaded signing.
  uint32_t mode = kOtbnEcdsaModeSideloadSign;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p256_sign_finalize(ecdsa_p256_signature_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read signature R out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarEcdsaR, result->r));

  // Read signature S out of OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarEcdsaS, result->s));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t ecdsa_p256_verify_start(const ecdsa_p256_signature_t *signature,
                                 const uint32_t digest[kP256ScalarWords],
                                 const p256_point_t *public_key) {
  // Load the ECDSA/P-256 app and set up data pointers
  HARDENED_TRY(otbn_load_app(kOtbnAppEcdsa));

  // Set mode so start() will jump into verifying.
  uint32_t mode = kOtbnEcdsaModeVerify;
  HARDENED_TRY(otbn_dmem_write(kOtbnEcdsaModeWords, &mode, kOtbnVarEcdsaMode));

  // Set the message digest.
  HARDENED_TRY(set_message_digest(digest));

  // Set the signature R.
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->r, kOtbnVarEcdsaR));

  // Set the signature S.
  HARDENED_TRY(otbn_dmem_write(kP256ScalarWords, signature->s, kOtbnVarEcdsaS));

  // Set the public key x coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->x, kOtbnVarEcdsaX));

  // Set the public key y coordinate.
  HARDENED_TRY(otbn_dmem_write(kP256CoordWords, public_key->y, kOtbnVarEcdsaY));

  // Start the OTBN routine.
  return otbn_execute();
}

status_t ecdsa_p256_verify_finalize(const ecdsa_p256_signature_t *signature,
                                    hardened_bool_t *result) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the status code out of DMEM (false if basic checks on the validity of
  // the signature and public key failed).
  uint32_t ok;
  HARDENED_TRY(otbn_dmem_read(1, kOtbnVarEcdsaOk, &ok));
  if (launder32(ok) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ok, kHardenedBoolTrue);

  // Read x_r (recovered R) out of OTBN dmem.
  uint32_t x_r[kP256ScalarWords];
  HARDENED_TRY(otbn_dmem_read(kP256ScalarWords, kOtbnVarEcdsaXr, x_r));

  *result = hardened_memeq(x_r, signature->r, kP256ScalarWords);

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}
