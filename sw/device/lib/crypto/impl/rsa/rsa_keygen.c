// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_keygen.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'k', 'g')

OTBN_DECLARE_APP_SYMBOLS(run_rsa_keygen);         // The OTBN RSA keygen binary.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_keygen, mode);   // Application mode.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_keygen, rsa_n);  // Public exponent n.
OTBN_DECLARE_SYMBOL_ADDR(run_rsa_keygen, rsa_d);  // Private exponent d.

static const otbn_app_t kOtbnAppRsaKeygen = OTBN_APP_T_INIT(run_rsa_keygen);
static const otbn_addr_t kOtbnVarRsaMode =
    OTBN_ADDR_T_INIT(run_rsa_keygen, mode);
static const otbn_addr_t kOtbnVarRsaN = OTBN_ADDR_T_INIT(run_rsa_keygen, rsa_n);
static const otbn_addr_t kOtbnVarRsaD = OTBN_ADDR_T_INIT(run_rsa_keygen, rsa_d);

enum {
  /* Fixed public exponent for generated keys. This exponent is 2^16 + 1, also
     known as "F4" because it's the fourth Fermat number. */
  kFixedPublicExponent = 65537,
  /* Number of words used to represent the application mode. */
  kOtbnRsaModeWords = 1,
};

// Available application modes. Must match the values from `run_rsa_keygen.s`.
// TODO: I think it's possible to pull these values directly from symbols in
// the binary. See:
//   hw/ip/otbn/util/otbn_objdump.py -t run_rsa_keygen.rv32embed.o
enum {
  kOtbnRsaMode2048 = 0x3b7,
  kOtbnRsaMode3072 = 0x4fa,
  kOtbnRsaMode4096 = 0x74d,
};

/**
 * Start the OTBN key generation program.
 *
 * @param mode Mode parameter for keygen.
 * @return Result of the operation.
 */
static status_t keygen_start(uint32_t mode) {
  // Load the RSA key generation app. Fails if OTBN is non-idle.
  HARDENED_TRY(otbn_load_app(kOtbnAppRsaKeygen));

  // Set mode and start OTBN.
  HARDENED_TRY(otbn_dmem_write(kOtbnRsaModeWords, &mode, kOtbnVarRsaMode));
  return otbn_execute();
}

/**
 * Finalize a key generation operation and read back the modulus and private
 * exponent.
 *
 * @param num_words Number of words for modulus and private exponent.
 * @param[out] n Buffer for the modulus.
 * @param[out] d Buffer for the private exponent.
 */
static status_t keygen_finalize(size_t num_words, uint32_t *n, uint32_t *d) {
  // Spin here waiting for OTBN to complete.
  HARDENED_TRY(otbn_busy_wait_for_done());

  // Read the public modulus (n) from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaN, n));

  // Read the private exponent (d) from OTBN dmem.
  HARDENED_TRY(otbn_dmem_read(num_words, kOtbnVarRsaD, d));

  // Wipe DMEM.
  HARDENED_TRY(otbn_dmem_sec_wipe());

  return OTCRYPTO_OK;
}

status_t rsa_keygen_2048_start(void) { return keygen_start(kOtbnRsaMode2048); }

status_t rsa_keygen_2048_finalize(rsa_2048_public_key_t *public_key,
                                  rsa_2048_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kRsa2048NumWords, private_key->n.data,
                               private_key->d.data));

  // Copy the modulus to the public key.
  hardened_memcpy(public_key->n.data, private_key->n.data,
                  ARRAYSIZE(private_key->n.data));

  // Set the public exponent to F4, the only exponent our key generation
  // algorithm supports.
  public_key->e = kFixedPublicExponent;

  return OTCRYPTO_OK;
}

status_t rsa_keygen_3072_start(void) { return keygen_start(kOtbnRsaMode3072); }

status_t rsa_keygen_3072_finalize(rsa_3072_public_key_t *public_key,
                                  rsa_3072_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kRsa3072NumWords, private_key->n.data,
                               private_key->d.data));

  // Copy the modulus to the public key.
  hardened_memcpy(public_key->n.data, private_key->n.data,
                  ARRAYSIZE(private_key->n.data));

  // Set the public exponent to F4, the only exponent our key generation
  // algorithm supports.
  public_key->e = kFixedPublicExponent;

  return OTCRYPTO_OK;
}

status_t rsa_keygen_4096_start(void) { return keygen_start(kOtbnRsaMode4096); }

status_t rsa_keygen_4096_finalize(rsa_4096_public_key_t *public_key,
                                  rsa_4096_private_key_t *private_key) {
  HARDENED_TRY(keygen_finalize(kRsa4096NumWords, private_key->n.data,
                               private_key->d.data));

  // Copy the modulus to the public key.
  hardened_memcpy(public_key->n.data, private_key->n.data,
                  ARRAYSIZE(private_key->n.data));

  // Set the public exponent to F4, the only exponent our key generation
  // algorithm supports.
  public_key->e = kFixedPublicExponent;

  return OTCRYPTO_OK;
}
