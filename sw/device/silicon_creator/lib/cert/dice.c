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
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

static ecdsa_p256_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};
static uint8_t cdi_0_tbs_buffer[kCdi0MaxTbsSizeBytes];
static cdi_0_sig_values_t cdi_0_cert_params = {
    .tbs = cdi_0_tbs_buffer,
    .tbs_size = kCdi0MaxTbsSizeBytes,
};
static uint8_t cdi_1_tbs_buffer[kCdi1MaxTbsSizeBytes];
static cdi_1_sig_values_t cdi_1_cert_params = {
    .tbs = cdi_1_tbs_buffer,
    .tbs_size = kCdi1MaxTbsSizeBytes,
};

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

// UDS (Creator) attestation key diverisfier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_diversification_t kUdsKeymgrDiversifier = {
    .salt =
        {
            0xabffa6a9,
            0xc781f1ad,
            0x4c1107ad,
            0xf9210d85,
            0x0931f555,
            0x6c5aef5d,
            0xb9ba4df0,
            0x77b248d2,
        },
    .version = 0,
};
// CDI_0 (OwnerIntermediate) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi0KeymgrDiversifier = {
    .salt =
        {
            0x3e5913c7,
            0x41156f1d,
            0x998ddb9f,
            0xfa334191,
            0x8a85380e,
            0xba76ca1a,
            0xdb17c4a7,
            0xfb8852dc,
        },
    .version = 0,
};
// CDI_1 (Owner) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi1KeymgrDiversifier = {
    .salt =
        {
            0x2d12c2e3,
            0x6acc6876,
            0x4bfb07ee,
            0xc45fc414,
            0x5d4fa9de,
            0xf295b128,
            0x50f49882,
            0xbbdefa29,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyUds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldUdsKeySeedIdx,
    .keymgr_diversifier = &kUdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi0KeySeedIdx,
    .keymgr_diversifier = &kCdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi1KeySeedIdx,
    .keymgr_diversifier = &kCdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

/**
 * Helper function to convert an attestation certificate signature from little
 * to big endian.
 */
static void curr_tbs_signature_le_to_be_convert(ecdsa_p256_signature_t *sig) {
  util_reverse_bytes(sig->r, kEcdsaP256SignatureComponentBytes);
  util_reverse_bytes(sig->s, kEcdsaP256SignatureComponentBytes);
}

rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  // Generate the TBS certificate.
  uds_tbs_values_t uds_cert_tbs_params = {
      .otp_creator_sw_cfg_hash =
          (unsigned char *)otp_creator_sw_cfg_measurement->digest,
      .otp_creator_sw_cfg_hash_size = kHmacDigestNumBytes,
      .otp_owner_sw_cfg_hash =
          (unsigned char *)otp_owner_sw_cfg_measurement->digest,
      .otp_owner_sw_cfg_hash_size = kHmacDigestNumBytes,
      .otp_rot_creator_auth_codesign_hash =
          (unsigned char *)otp_rot_creator_auth_codesign_measurement->digest,
      .otp_rot_creator_auth_codesign_hash_size = kHmacDigestNumBytes,
      .otp_rot_creator_auth_state_hash =
          (unsigned char *)otp_rot_creator_auth_state_measurement->digest,
      .otp_rot_creator_auth_state_hash_size = kHmacDigestNumBytes,
      .debug_flag = is_debug_exposed(),
      .creator_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .auth_key_key_id = (unsigned char *)key_ids->endorsement->digest,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_ec_x = (unsigned char *)uds_pubkey->x,
      .creator_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .creator_pub_key_ec_y = (unsigned char *)uds_pubkey->y,
      .creator_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
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
  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_cert_tbs_params = {
      .rom_ext_hash = (unsigned char *)rom_ext_measurement->digest,
      .rom_ext_hash_size = kDiceMeasurementSizeInBytes,
      .rom_ext_security_version = rom_ext_security_version,
      .owner_intermediate_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .owner_intermediate_pub_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_id = (unsigned char *)key_ids->endorsement->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_ec_x = (unsigned char *)cdi_0_pubkey->x,
      .owner_intermediate_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .owner_intermediate_pub_key_ec_y = (unsigned char *)cdi_0_pubkey->y,
      .owner_intermediate_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
  };
  HARDENED_RETURN_IF_ERROR(cdi_0_build_tbs(&cdi_0_cert_tbs_params,
                                           cdi_0_cert_params.tbs,
                                           &cdi_0_cert_params.tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_0_cert_params.tbs, cdi_0_cert_params.tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  curr_tbs_signature_le_to_be_convert(&curr_tbs_signature);
  cdi_0_cert_params.cert_signature_r = (unsigned char *)curr_tbs_signature.r;
  cdi_0_cert_params.cert_signature_r_size = kAttestationSignatureBytes / 2;
  cdi_0_cert_params.cert_signature_s = (unsigned char *)curr_tbs_signature.s;
  cdi_0_cert_params.cert_signature_s_size = kAttestationSignatureBytes / 2;
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
  // Generate the TBS certificate.
  cdi_1_tbs_values_t cdi_1_cert_tbs_params = {
      .owner_hash = (unsigned char *)owner_measurement->digest,
      .owner_hash_size = kDiceMeasurementSizeInBytes,
      .owner_manifest_hash =
          (unsigned char *)owner_manifest_measurement->digest,
      .owner_manifest_hash_size = kDiceMeasurementSizeInBytes,
      .owner_security_version = owner_security_version,
      .owner_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .owner_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_id =
          (unsigned char *)key_ids->endorsement->digest,
      .owner_intermediate_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_pub_key_ec_x = (unsigned char *)cdi_1_pubkey->x,
      .owner_pub_key_ec_x_size = kEcdsaP256PublicKeyCoordBytes,
      .owner_pub_key_ec_y = (unsigned char *)cdi_1_pubkey->y,
      .owner_pub_key_ec_y_size = kEcdsaP256PublicKeyCoordBytes,
  };
  HARDENED_RETURN_IF_ERROR(cdi_1_build_tbs(&cdi_1_cert_tbs_params,
                                           cdi_1_cert_params.tbs,
                                           &cdi_1_cert_params.tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_1_cert_params.tbs, cdi_1_cert_params.tbs_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  curr_tbs_signature_le_to_be_convert(&curr_tbs_signature);
  cdi_1_cert_params.cert_signature_r = (unsigned char *)curr_tbs_signature.r;
  cdi_1_cert_params.cert_signature_r_size = kAttestationSignatureBytes / 2;
  cdi_1_cert_params.cert_signature_s = (unsigned char *)curr_tbs_signature.s;
  cdi_1_cert_params.cert_signature_s_size = kAttestationSignatureBytes / 2;
  HARDENED_RETURN_IF_ERROR(
      cdi_1_build_cert(&cdi_1_cert_params, cert, cert_size));

  // Save the CDI_1 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier));

  return kErrorOk;
}
