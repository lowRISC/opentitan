// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_KEYS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/sigverify/mldsa_key.h"

// Keymgr configurations for deriving attestation keys.
typedef struct keygen_params {
  const sc_keymgr_ecc_key_t *ecc_cfg;
  const sc_keymgr_ecc_key_t *mldsa_44_cfg;
  const sc_keymgr_ecc_key_t *mldsa_87_cfg;
} keygen_params_t;

extern const keygen_params_t kDiceMldsaUdsKeygenParams;

/**
 * Derives a 256-bit ML-DSA private key seed using the SP800-133r3 scheme.
 *
 * @param params Key generation parameters.
 * @param alg_params The ML-DSA parameter set.
 * @param[out] seed_output Derived 256-bit ML-DSA key seed.
 */
OT_WARN_UNUSED_RESULT rom_error_t dice_mldsa_derive_seed(
    const keygen_params_t *params, mldsa_parameter_set_t alg_params,
    keymgr_binding_value_t *seed_output);

/**
 * Derives a 256-bit ML-DSA certificate ID from a seed.
 *
 * @param seed The ML-DSA key seed.
 * @param[out] id The computed public key ID.
 */
void dice_mldsa_key_id_get(const hmac_key_t *seed, hmac_digest_t *id);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_KEYS_H_
