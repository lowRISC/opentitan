// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/tpm.h"

#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

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
