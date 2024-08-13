// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/tpm.h"

#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
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
  tpm_ek_tbs_values_t tpm_ek_tbs_params = {
      .auth_key_key_id = (unsigned char *)key_ids->endorsement,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .tpm_ek_pub_key_ec_x = (unsigned char *)tpm_ek_pubkey->x,
      .tpm_ek_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_ek_pub_key_ec_y = (unsigned char *)tpm_ek_pubkey->y,
      .tpm_ek_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_ek_pub_key_id = (unsigned char *)key_ids->cert,
      .tpm_ek_pub_key_id_size = kCertKeyIdSizeInBytes,
      .tpm_version = "0.0.1",
      .tpm_version_len = 5,
      .tpm_vendor = "Nuvoton",
      .tpm_vendor_len = 7,
      .tpm_model = "Ti50",
      .tpm_model_len = 4,
  };

  HARDENED_RETURN_IF_ERROR(
      tpm_ek_build_tbs(&tpm_ek_tbs_params, tpm_ek_tbs, tpm_ek_tbs_size));

  return kErrorOk;
}
