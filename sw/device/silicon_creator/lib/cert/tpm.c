// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/tpm.h"

#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

const sc_keymgr_diversification_t kTpmEkKeymgrDiversifier = {
    .salt =
        {
            0x3fd3bc42,
            0x5a401205,
            0xfa3fbe70,
            0xc1d035da,
            0x87292fe6,
            0x4d94f30f,
            0x2e954c30,
            0x351c28f1,
        },
    .version = 0,
};
const sc_keymgr_ecc_key_t kTpmKeyEk = {
    .type = kScKeymgrKeyTypeSealing,
    .keygen_seed_idx = kFlashInfoFieldTpmEkKeySeedIdx,
    .keymgr_diversifier = &kTpmEkKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

rom_error_t tpm_ek_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *tpm_ek_pubkey,
                                  uint8_t *tpm_ek_tbs,
                                  size_t *tpm_ek_tbs_size) {
  // We initialize these strings with character arrays (as opposed to the more
  // readable string literal) as we need them to be non-null terminated.
  // Additionally, they are not declared `const` as the TBS cert generator does
  // not accept const params.
  static char tpm_version[] = {'0', '.', '0', '.', '1'};
  static char tpm_vendor[] = {'N', 'u', 'v', 'o', 't', 'o', 'n'};
  static char tpm_model[] = {'T', 'i', '5', '0'};

  tpm_ek_tbs_values_t tpm_ek_tbs_params = {0};

  TEMPLATE_SET(tpm_ek_tbs_params, TpmEk, TpmEkPubKeyEcX, tpm_ek_pubkey->x);
  TEMPLATE_SET(tpm_ek_tbs_params, TpmEk, TpmEkPubKeyEcY, tpm_ek_pubkey->y);
  TEMPLATE_SET(tpm_ek_tbs_params, TpmEk, TpmVersion, tpm_version);
  TEMPLATE_SET(tpm_ek_tbs_params, TpmEk, TpmVendor, tpm_vendor);
  TEMPLATE_SET(tpm_ek_tbs_params, TpmEk, TpmModel, tpm_model);

  TEMPLATE_SET_TRUNCATED(tpm_ek_tbs_params, TpmEk, AuthKeyKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(tpm_ek_tbs_params, TpmEk, TpmEkPubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);

  HARDENED_RETURN_IF_ERROR(
      tpm_ek_build_tbs(&tpm_ek_tbs_params, tpm_ek_tbs, tpm_ek_tbs_size));

  return kErrorOk;
}
