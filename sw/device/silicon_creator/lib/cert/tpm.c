// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/tpm.h"

#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
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
const sc_keymgr_diversification_t kTpmCekKeymgrDiversifier = {
    .salt =
        {
            0x8a5d086c,
            0xcbe850b4,
            0x9aeab7c0,
            0x8faf44a4,
            0xc5bf5663,
            0x217359ab,
            0xb42fe0fd,
            0xd06ad674,
        },
    .version = 0,

};
const sc_keymgr_diversification_t kTpmCikKeymgrDiversifier = {
    .salt =
        {
            0x9d664be2,
            0x8a9739a9,
            0xe6f815bd,
            0x8940348b,
            0x6ee241f7,
            0xea5b14cd,
            0x9e81908b,
            0x15ff16f0,
        },
    .version = 0,
};
const sc_keymgr_ecc_key_t kTpmKeyEk = {
    .type = kScKeymgrKeyTypeSealing,
    .keygen_seed_idx = kFlashInfoFieldTpmEkKeySeedIdx,
    .keymgr_diversifier = &kTpmEkKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};
const sc_keymgr_ecc_key_t kTpmKeyCek = {
    .type = kScKeymgrKeyTypeSealing,
    .keygen_seed_idx = kFlashInfoFieldTpmCekKeySeedIdx,
    .keymgr_diversifier = &kTpmCekKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};
const sc_keymgr_ecc_key_t kTpmKeyCik = {
    .type = kScKeymgrKeyTypeSealing,
    .keygen_seed_idx = kFlashInfoFieldTpmCikKeySeedIdx,
    .keymgr_diversifier = &kTpmCikKeymgrDiversifier,
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

rom_error_t tpm_cek_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                   ecdsa_p256_public_key_t *tpm_cek_pubkey,
                                   uint8_t *tpm_cek_tbs,
                                   size_t *tpm_cek_tbs_size) {
  tpm_cek_tbs_values_t tpm_cek_tbs_params = {
      .auth_key_key_id = (unsigned char *)key_ids->endorsement,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .tpm_cek_pub_key_ec_x = (unsigned char *)tpm_cek_pubkey->x,
      .tpm_cek_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_cek_pub_key_ec_y = (unsigned char *)tpm_cek_pubkey->y,
      .tpm_cek_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_cek_pub_key_id = (unsigned char *)key_ids->cert,
      .tpm_cek_pub_key_id_size = kCertKeyIdSizeInBytes,
  };

  HARDENED_RETURN_IF_ERROR(
      tpm_cek_build_tbs(&tpm_cek_tbs_params, tpm_cek_tbs, tpm_cek_tbs_size));

  return kErrorOk;
}

rom_error_t tpm_cik_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                   ecdsa_p256_public_key_t *tpm_cik_pubkey,
                                   uint8_t *tpm_cik_tbs,
                                   size_t *tpm_cik_tbs_size) {
  tpm_cik_tbs_values_t tpm_cik_tbs_params = {
      .auth_key_key_id = (unsigned char *)key_ids->endorsement,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .tpm_cik_pub_key_ec_x = (unsigned char *)tpm_cik_pubkey->x,
      .tpm_cik_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_cik_pub_key_ec_y = (unsigned char *)tpm_cik_pubkey->y,
      .tpm_cik_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
      .tpm_cik_pub_key_id = (unsigned char *)key_ids->cert,
      .tpm_cik_pub_key_id_size = kCertKeyIdSizeInBytes,
  };

  HARDENED_RETURN_IF_ERROR(
      tpm_cik_build_tbs(&tpm_cik_tbs_params, tpm_cik_tbs, tpm_cik_tbs_size));

  return kErrorOk;
}
