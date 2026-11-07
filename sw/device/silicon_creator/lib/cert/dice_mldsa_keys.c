// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice_mldsa_keys.h"

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/seeds.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/sigverify/mldsa_key.h"

const keygen_params_t kDiceMldsaUdsKeygenParams = {
    .ecc_cfg = &kDiceKeyUds,
    .mldsa_44_cfg = &kDiceKeyMldsa44Uds,
    .mldsa_87_cfg = &kDiceKeyMldsa87Uds,
};

OT_WARN_UNUSED_RESULT rom_error_t dice_mldsa_derive_seed(
    const keygen_params_t *params, mldsa_parameter_set_t alg_params,
    keymgr_binding_value_t *seed_output) {
  const sc_keymgr_ecc_key_t *mldsa_cfg = NULL;
  switch (alg_params) {
    case kMldsaParameterSet44:
      mldsa_cfg = params->mldsa_44_cfg;
      break;
    case kMldsaParameterSet87:
      mldsa_cfg = params->mldsa_87_cfg;
      break;
    default:
      return kErrorDiceMldsaParamsUnsupported;
  }
  HARDENED_RETURN_IF_ERROR(
      sc_keymgr_generate_key_sw(kScKeymgrKeyTypeAttestation,
                                *mldsa_cfg->keymgr_diversifier, seed_output));

  uint32_t additional_seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(
      mldsa_cfg->keygen_seed_idx, additional_seed));

  for (size_t i = 0; i < sizeof(seed_output->data) / sizeof(uint32_t); ++i) {
    seed_output->data[i] ^= additional_seed[i];
  }

  return kErrorOk;
}

void dice_mldsa_key_id_get(const hmac_key_t *seed, hmac_digest_t *id) {
  hmac_hmac_sha256("ID", 2, *seed, /*big_endian_digest=*/true, id);
}
