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
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

static ecdsa_p256_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};

static uint8_t cdi_0_tbs_buffer[kCdi0MaxTbsSizeBytes];
static uint8_t cdi_1_tbs_buffer[kCdi1MaxTbsSizeBytes];

const dice_cert_format_t kDiceCertFormat = kDiceCertFormatX509TcbInfo;

static_assert(kDiceMeasurementSizeInBytes == 32,
              "The DICE attestation measurement size should equal the size of "
              "the keymgr binding registers.");

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

/**
 * Returns true if the OwnerSw is booting outside of prod ladder.
 */
static bool get_debug_mode_cdi1(owner_app_domain_t key_domain) {
  if (launder32(key_domain) != kOwnerAppDomainProd) {
    return true;
  }
  HARDENED_CHECK_EQ(key_domain, kOwnerAppDomainProd);
  return false;
}

rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  // Generate the TBS certificate.
  uds_tbs_values_t uds_tbs_params = {0};

  TEMPLATE_SET(uds_tbs_params, Uds, OtpCreatorSwCfgHash,
               otp_creator_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpOwnerSwCfgHash,
               otp_owner_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthCodesignHash,
               otp_rot_creator_auth_codesign_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthStateHash,
               otp_rot_creator_auth_state_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, DebugFlag, is_debug_exposed());
  TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyEcX, uds_pubkey->x);
  TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyEcY, uds_pubkey->y);

  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, CreatorPubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, AuthKeyKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);

  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_tbs_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  uint32_t rom_ext_security_version_be =
      __builtin_bswap32(rom_ext_security_version);
  hmac_digest_t rom_ext_hash = *rom_ext_measurement;
  util_reverse_bytes(&rom_ext_hash, sizeof(rom_ext_hash));

  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_tbs_params = {0};

  TEMPLATE_SET(cdi_0_tbs_params, Cdi0, RomExtHash, rom_ext_hash.digest);
  TEMPLATE_SET(cdi_0_tbs_params, Cdi0, RomExtSecurityVersion,
               &rom_ext_security_version_be);
  TEMPLATE_SET(cdi_0_tbs_params, Cdi0, OwnerIntermediatePubKeyEcX,
               cdi_0_pubkey->x);
  TEMPLATE_SET(cdi_0_tbs_params, Cdi0, OwnerIntermediatePubKeyEcY,
               cdi_0_pubkey->y);

  TEMPLATE_SET_TRUNCATED(cdi_0_tbs_params, Cdi0, OwnerIntermediatePubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(cdi_0_tbs_params, Cdi0, CreatorPubKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);

  size_t tbs_size = kCdi0MaxTbsSizeBytes;
  HARDENED_RETURN_IF_ERROR(
      cdi_0_build_tbs(&cdi_0_tbs_params, cdi_0_tbs_buffer, &tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_0_tbs_buffer, tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  cdi_0_sig_values_t cdi_0_params = {0};
  TEMPLATE_SET(cdi_0_params, Cdi0, Tbs, cdi_0_tbs_buffer);
  // Asserts that tbs is fixed-length, so we don't need to set tbs_size.
  TEMPLATE_ASSERT_FIXED_LENGTH(Cdi0, Tbs);
  TEMPLATE_SET(cdi_0_params, Cdi0, CertSignatureR, curr_tbs_signature.r);
  TEMPLATE_SET(cdi_0_params, Cdi0, CertSignatureS, curr_tbs_signature.s);

  HARDENED_RETURN_IF_ERROR(cdi_0_build_cert(&cdi_0_params, cert, cert_size));

  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  owner_app_domain_t key_domain,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  uint32_t owner_security_version_be =
      __builtin_bswap32(owner_security_version);
  hmac_digest_t owner_hash = *owner_measurement;
  hmac_digest_t owner_manifest_hash = *owner_manifest_measurement;
  util_reverse_bytes(&owner_hash, sizeof(owner_hash));
  util_reverse_bytes(&owner_manifest_hash, sizeof(owner_manifest_hash));

  // Generate the TBS certificate.
  cdi_1_tbs_values_t cdi_1_tbs_params = {0};

  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, OwnerHash, owner_hash.digest);
  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, OwnerManifestHash,
               owner_manifest_hash.digest);
  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, OwnerSecurityVersion,
               &owner_security_version_be);
  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, DebugFlag,
               get_debug_mode_cdi1(key_domain));
  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, OwnerPubKeyEcX, cdi_1_pubkey->x);
  TEMPLATE_SET(cdi_1_tbs_params, Cdi1, OwnerPubKeyEcY, cdi_1_pubkey->y);

  TEMPLATE_SET_TRUNCATED(cdi_1_tbs_params, Cdi1, OwnerPubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(cdi_1_tbs_params, Cdi1, OwnerIntermediatePubKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);

  size_t tbs_size = kCdi1MaxTbsSizeBytes;
  HARDENED_RETURN_IF_ERROR(
      cdi_1_build_tbs(&cdi_1_tbs_params, cdi_1_tbs_buffer, &tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_1_tbs_buffer, tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  cdi_1_sig_values_t cdi_1_params = {0};
  TEMPLATE_SET(cdi_1_params, Cdi1, Tbs, cdi_1_tbs_buffer);
  // Asserts that tbs is fixed-length, so we don't need to set tbs_size.
  TEMPLATE_ASSERT_FIXED_LENGTH(Cdi1, Tbs);
  TEMPLATE_SET(cdi_1_params, Cdi1, CertSignatureR, curr_tbs_signature.r);
  TEMPLATE_SET(cdi_1_params, Cdi1, CertSignatureS, curr_tbs_signature.s);

  HARDENED_RETURN_IF_ERROR(cdi_1_build_cert(&cdi_1_params, cert, cert_size));

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

  // Assert the digest is not shorter then the key id before truncation.
  static_assert(sizeof(pubkey_id->digest) >= sizeof(cert_key_id_t),
                "Pubkey Id is too short.");

  return cert_x509_asn1_check_serial_number(
      cert_obj->cert_body_p, cert_obj->cert_body_size,
      (cert_key_id_t *)pubkey_id->digest, cert_valid_output);
}
