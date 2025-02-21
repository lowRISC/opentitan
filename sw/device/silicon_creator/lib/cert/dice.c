// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

static ecdsa_p256_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};
static uint8_t cdi_0_tbs_buffer[kCdi0MaxTbsSizeBytes];
static cdi_0_sig_values_t cdi_0_cert_params = {
    .tbs = cdi_0_tbs_buffer,
    .cert_signature_r = (unsigned char *)curr_tbs_signature.r,
    .cert_signature_s = (unsigned char *)curr_tbs_signature.s,
};
static uint8_t cdi_1_tbs_buffer[kCdi1MaxTbsSizeBytes];
static cdi_1_sig_values_t cdi_1_cert_params = {
    .tbs = cdi_1_tbs_buffer,
    .cert_signature_r = (unsigned char *)curr_tbs_signature.r,
    .cert_signature_s = (unsigned char *)curr_tbs_signature.s,
};

const dice_cert_format_t kDiceCertFormat = kDiceCertFormatX509TcbInfo;

static_assert(kDiceMeasurementSizeInBytes == 32,
              "The DICE attestation measurement size should equal the size of "
              "the keymgr binding registers.");

/**
 * Helpers for writing static assertions on variable array sizes.
 */
#define ASSERT_SIZE_EQ(actual, expected) \
  static_assert(actual == expected, "Invalid variable size.");

#define ASSERT_SIZE_GE(actual, expected) \
  static_assert(actual >= expected, "Invalid variable size.");

/**
 * Returns true if debug (JTAG) access is exposed in the current LC state.
 */
static bool is_debug_exposed(void) {
  lifecycle_state_t lc_state = lifecycle_state_get();
  if (lc_state == kLcStateProd || lc_state == kLcStateProdEnd) {
    return false;
  }
  return true;
}

rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  ASSERT_SIZE_EQ(sizeof(otp_creator_sw_cfg_measurement->digest),
                 kUdsExactOtpCreatorSwCfgHashSizeBytes);
  ASSERT_SIZE_EQ(sizeof(otp_owner_sw_cfg_measurement->digest),
                 kUdsExactOtpOwnerSwCfgHashSizeBytes);
  ASSERT_SIZE_EQ(sizeof(otp_rot_creator_auth_codesign_measurement->digest),
                 kUdsExactOtpRotCreatorAuthCodesignHashSizeBytes);
  ASSERT_SIZE_EQ(sizeof(otp_rot_creator_auth_state_measurement->digest),
                 kUdsExactOtpRotCreatorAuthStateHashSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->cert->digest),
                 kUdsExactCreatorPubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes, kUdsExactCreatorPubKeyIdSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->endorsement->digest),
                 kUdsExactAuthKeyKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes, kUdsExactAuthKeyKeyIdSizeBytes);
  ASSERT_SIZE_EQ(sizeof(uds_pubkey->x), kUdsExactCreatorPubKeyEcXSizeBytes);
  ASSERT_SIZE_EQ(sizeof(uds_pubkey->y), kUdsExactCreatorPubKeyEcYSizeBytes);

  // Generate the TBS certificate.
  uds_tbs_values_t uds_cert_tbs_params = {
      .otp_creator_sw_cfg_hash =
          (unsigned char *)otp_creator_sw_cfg_measurement->digest,
      .otp_owner_sw_cfg_hash =
          (unsigned char *)otp_owner_sw_cfg_measurement->digest,
      .otp_rot_creator_auth_codesign_hash =
          (unsigned char *)otp_rot_creator_auth_codesign_measurement->digest,
      .otp_rot_creator_auth_state_hash =
          (unsigned char *)otp_rot_creator_auth_state_measurement->digest,
      .debug_flag = is_debug_exposed(),
      .creator_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .auth_key_key_id = (unsigned char *)key_ids->endorsement->digest,
      .creator_pub_key_ec_x = (unsigned char *)uds_pubkey->x,
      .creator_pub_key_ec_y = (unsigned char *)uds_pubkey->y,
  };
  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_cert_tbs_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  ASSERT_SIZE_EQ(sizeof(rom_ext_measurement->digest),
                 kCdi0ExactRomExtHashSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->cert->digest),
                 kCdi0ExactOwnerIntermediatePubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes,
                 kCdi0ExactOwnerIntermediatePubKeyIdSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->endorsement->digest),
                 kCdi0ExactOwnerIntermediatePubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes, kCdi0ExactCreatorPubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(sizeof(cdi_0_pubkey->x),
                 kCdi0ExactOwnerIntermediatePubKeyEcXSizeBytes);
  ASSERT_SIZE_EQ(sizeof(cdi_0_pubkey->y),
                 kCdi0ExactOwnerIntermediatePubKeyEcYSizeBytes);

  uint32_t rom_ext_security_version_be =
      __builtin_bswap32(rom_ext_security_version);

  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_cert_tbs_params = {
      .rom_ext_hash = (unsigned char *)rom_ext_measurement->digest,
      .rom_ext_security_version = (unsigned char *)&rom_ext_security_version_be,
      .owner_intermediate_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .creator_pub_key_id = (unsigned char *)key_ids->endorsement->digest,
      .owner_intermediate_pub_key_ec_x = (unsigned char *)cdi_0_pubkey->x,
      .owner_intermediate_pub_key_ec_y = (unsigned char *)cdi_0_pubkey->y,
  };

  size_t tbs_size = kCdi0MaxTbsSizeBytes;
  HARDENED_RETURN_IF_ERROR(cdi_0_build_tbs(&cdi_0_cert_tbs_params,
                                           cdi_0_cert_params.tbs, &tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_0_cert_params.tbs, tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  ASSERT_SIZE_EQ(sizeof(curr_tbs_signature.r),
                 kCdi0ExactCertSignatureRSizeBytes);
  ASSERT_SIZE_EQ(sizeof(curr_tbs_signature.s),
                 kCdi0ExactCertSignatureSSizeBytes);

  HARDENED_RETURN_IF_ERROR(
      cdi_0_build_cert(&cdi_0_cert_params, cert, cert_size));

  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  ASSERT_SIZE_EQ(sizeof(owner_measurement->digest),
                 kCdi1ExactOwnerHashSizeBytes);
  ASSERT_SIZE_EQ(sizeof(owner_manifest_measurement->digest),
                 kCdi1ExactOwnerManifestHashSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->cert->digest),
                 kCdi1ExactOwnerPubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes, kCdi1ExactOwnerPubKeyIdSizeBytes);
  ASSERT_SIZE_GE(sizeof(key_ids->endorsement->digest),
                 kCdi1ExactOwnerIntermediatePubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(kCertKeyIdSizeInBytes,
                 kCdi1ExactOwnerIntermediatePubKeyIdSizeBytes);
  ASSERT_SIZE_EQ(sizeof(cdi_1_pubkey->x), kCdi1ExactOwnerPubKeyEcXSizeBytes);
  ASSERT_SIZE_EQ(sizeof(cdi_1_pubkey->y), kCdi1ExactOwnerPubKeyEcYSizeBytes);

  uint32_t owner_security_version_be =
      __builtin_bswap32(owner_security_version);

  // Generate the TBS certificate.
  cdi_1_tbs_values_t cdi_1_cert_tbs_params = {
      .owner_hash = (unsigned char *)owner_measurement->digest,
      .owner_manifest_hash =
          (unsigned char *)owner_manifest_measurement->digest,
      .owner_security_version = (unsigned char *)&owner_security_version_be,
      .owner_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .owner_intermediate_pub_key_id =
          (unsigned char *)key_ids->endorsement->digest,
      .owner_pub_key_ec_x = (unsigned char *)cdi_1_pubkey->x,
      .owner_pub_key_ec_y = (unsigned char *)cdi_1_pubkey->y,
  };

  size_t tbs_size = kCdi1MaxTbsSizeBytes;
  HARDENED_RETURN_IF_ERROR(cdi_1_build_tbs(&cdi_1_cert_tbs_params,
                                           cdi_1_cert_params.tbs, &tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_1_cert_params.tbs, tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  ASSERT_SIZE_EQ(sizeof(curr_tbs_signature.r),
                 kCdi0ExactCertSignatureRSizeBytes);
  ASSERT_SIZE_EQ(sizeof(curr_tbs_signature.s),
                 kCdi0ExactCertSignatureSSizeBytes);

  HARDENED_RETURN_IF_ERROR(
      cdi_1_build_cert(&cdi_1_cert_params, cert, cert_size));

  // Save the CDI_1 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_cert_check_valid(const perso_tlv_cert_obj_t *cert_obj,
                                  const hmac_digest_t *pubkey_id,
                                  const ecdsa_p256_public_key_t *pubkey,
                                  hardened_bool_t *cert_valid_output) {
  // The function prototype is shared across X.509 and CWT cert formats.
  // For X.509, we only check the serial_number but not public key contents.
  OT_DISCARD(pubkey);

  return cert_x509_asn1_check_serial_number(
      cert_obj->cert_body_p, 0, (uint8_t *)pubkey_id->digest, cert_valid_output,
      /*out_cert_size=*/NULL);
}
