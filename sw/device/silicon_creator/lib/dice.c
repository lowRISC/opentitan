// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/dice.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"    // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"    // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"      // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

#include "otp_ctrl_regs.h"  // Generated.

enum {
  /**
   * Size of the largest OTP partition to be measured.
   */
  kDiceMeasuredOtpPartitionMaxSizeIn32bitWords =
      (OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
       OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
      sizeof(uint32_t),
};

static uint32_t otp_state[kDiceMeasuredOtpPartitionMaxSizeIn32bitWords] = {0};
static attestation_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};
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

// clang-format off
static_assert(
    OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE >= OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE &&
    OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE >= OTP_CTRL_PARAM_HW_CFG_SIZE,
    "The largest DICE measured OTP partition is no longer the "
    "OwnerSwCfg partition. Update the "
    "kDiceMeasuredOtpPartitionMaxSizeIn32bitWords constant.");
// clang-format on

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
 * Helper function to convert a buffer of bytes from little to big endian in
 * place.
 */
static void le_be_buf_format(unsigned char *buf, size_t num_bytes) {
  unsigned char temp;
  for (size_t i = 0; i < (num_bytes / 2); ++i) {
    temp = buf[i];
    buf[i] = buf[num_bytes - i - 1];
    buf[num_bytes - i - 1] = temp;
  }
}

/**
 * Helper function to convert an attestation public key from little to big
 * endian in place.
 */
static void curr_pubkey_le_to_be_convert(attestation_public_key_t *pubkey) {
  le_be_buf_format((unsigned char *)pubkey->x, kAttestationPublicKeyCoordBytes);
  le_be_buf_format((unsigned char *)pubkey->y, kAttestationPublicKeyCoordBytes);
}

/**
 * Function generating a DICE or TPM certificate key pair. If successful, the
 * generated public key is saved at pubkey.
 */
static rom_error_t common_attestation_keygen(
    otbn_boot_attestation_key_type_t key_type,
    const keymgr_diversification_t *diversifier, attestation_key_seed_t seed,
    keymgr_state_t desired_keymgr_state, hmac_digest_t *pubkey_id,
    attestation_public_key_t *pubkey) {
  HARDENED_RETURN_IF_ERROR(keymgr_state_check(desired_keymgr_state));

  // Generate / sideload key material into OTBN, and generate the ECC keypair.
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_keygen(seed, key_type, *diversifier, pubkey));

  // Keys are represented in certificates in big endian format, but the key is
  // output from OTBN in little endian format, so we convert the key to
  // big endian format.
  curr_pubkey_le_to_be_convert(pubkey);

  // Generate the key ID.
  hmac_sha256(pubkey, kAttestationPublicKeyCoordBytes * 2, pubkey_id);

  return kErrorOk;
}

/**
 * Function preparing parameters for generating DICE attestation keys.
 */
rom_error_t dice_attestation_keygen(dice_key_t desired_key,
                                    hmac_digest_t *pubkey_id,
                                    attestation_public_key_t *pubkey) {
  attestation_key_seed_t otbn_ecc_keygen_seed;
  const keymgr_diversification_t *keymgr_diversifier;
  keymgr_state_t desired_state;

  switch (desired_key) {
    case kDiceKeyUds:
      desired_state = kKeymgrStateCreatorRootKey;
      keymgr_diversifier = &kUdsKeymgrDiversifier;
      otbn_ecc_keygen_seed = kUdsAttestationKeySeed;
      break;
    case kDiceKeyCdi0:
      desired_state = kKeymgrStateOwnerIntermediateKey;
      keymgr_diversifier = &kCdi0KeymgrDiversifier;
      otbn_ecc_keygen_seed = kCdi0AttestationKeySeed;
      break;
    case kDiceKeyCdi1:
      desired_state = kKeymgrStateOwnerKey;
      keymgr_diversifier = &kCdi1KeymgrDiversifier;
      otbn_ecc_keygen_seed = kCdi1AttestationKeySeed;
      break;
    default:
      return kErrorDiceInvalidArgument;
  };
  return common_attestation_keygen(kOtbnBootAttestationKeyTypeDice,
                                   keymgr_diversifier, otbn_ecc_keygen_seed,
                                   desired_state, pubkey_id, pubkey);
}

/**
 * Function preparing parameters for generating TPM keys.
 */
rom_error_t tpm_cert_keygen(tpm_key_t desired_key, hmac_digest_t *pubkey_id,
                            attestation_public_key_t *pubkey) {
  attestation_key_seed_t otbn_ecc_keygen_seed;
  const keymgr_diversification_t *keymgr_diversifier;

  switch (desired_key) {
    case kTpmKeyEk:
      keymgr_diversifier = &kTpmEkKeymgrDiversifier;
      otbn_ecc_keygen_seed = kTpmEkAttestationKeySeed;
      break;
    case kTpmKeyCek:
      keymgr_diversifier = &kTpmCekKeymgrDiversifier;
      otbn_ecc_keygen_seed = kTpmCekAttestationKeySeed;
      break;
    case kTpmKeyCik:
      keymgr_diversifier = &kTpmCikKeymgrDiversifier;
      otbn_ecc_keygen_seed = kTpmCikAttestationKeySeed;
      break;
    default:
      return kErrorDiceInvalidArgument;
  };
  return common_attestation_keygen(kOtbnBootAttestationKeyTypeTpm,
                                   keymgr_diversifier, otbn_ecc_keygen_seed,
                                   kKeymgrStateOwnerKey, pubkey_id, pubkey);
}

/**
 * Helper function to convert an attestation certificate signature from little
 * to big endian.
 */
static void curr_tbs_signature_le_to_be_convert(attestation_signature_t *sig) {
  le_be_buf_format((unsigned char *)sig->r,
                   kAttestationSignatureComponentBytes);
  le_be_buf_format((unsigned char *)sig->s,
                   kAttestationSignatureComponentBytes);
}

/**
 * Helper function to compute measurements of various OTP partitions that are to
 * be included in attestation certificates.
 */
static void measure_otp_partition(otp_partition_t partition,
                                  hmac_digest_t *measurement) {
  // Compute the digest.
  otp_dai_read(partition, /*address=*/0, otp_state,
               kOtpPartitions[partition].size / sizeof(uint32_t));
  hmac_sha256(otp_state, kOtpPartitions[partition].size, measurement);

  // Check the digest matches what is stored in OTP (for partitions that are
  // locked via software computed digest).
  if (partition == kOtpPartitionCreatorSwCfg ||
      partition == kOtpPartitionOwnerSwCfg) {
    uint64_t expected_digest = otp_partition_digest_read(partition);
    uint32_t digest_hi = expected_digest >> 32;
    uint32_t digest_lo = expected_digest & UINT32_MAX;
    HARDENED_CHECK_EQ(digest_hi, measurement->digest[1]);
    HARDENED_CHECK_EQ(digest_lo, measurement->digest[0]);
  }
}

rom_error_t dice_uds_tbs_cert_build(dice_cert_key_id_pair_t *key_ids,
                                    attestation_public_key_t *uds_pubkey,
                                    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  // Measure OTP partitions.
  hmac_digest_t otp_creator_sw_cfg_measurement = {.digest = {0}};
  hmac_digest_t otp_owner_sw_cfg_measurement = {.digest = {0}};
  hmac_digest_t otp_hw_cfg_measurement = {.digest = {0}};
  measure_otp_partition(kOtpPartitionCreatorSwCfg,
                        &otp_creator_sw_cfg_measurement);
  measure_otp_partition(kOtpPartitionOwnerSwCfg, &otp_owner_sw_cfg_measurement);
  measure_otp_partition(kOtpPartitionHwCfg, &otp_hw_cfg_measurement);

  // Generate the TBS certificate.
  uds_tbs_values_t uds_cert_tbs_params = {
      .otp_creator_sw_cfg_hash =
          (unsigned char *)otp_creator_sw_cfg_measurement.digest,
      .otp_creator_sw_cfg_hash_size = kHmacDigestNumBytes,
      .otp_owner_sw_cfg_hash =
          (unsigned char *)otp_owner_sw_cfg_measurement.digest,
      .otp_owner_sw_cfg_hash_size = kHmacDigestNumBytes,
      .otp_hw_cfg_hash = (unsigned char *)otp_hw_cfg_measurement.digest,
      .otp_hw_cfg_hash_size = kHmacDigestNumBytes,
      .debug_flag = is_debug_exposed(),
      .creator_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .creator_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
      .auth_key_key_id = (unsigned char *)key_ids->endorsement->digest,
      .auth_key_key_id_size = kDiceCertKeyIdSizeInBytes,
      .creator_pub_key_ec_x = (unsigned char *)uds_pubkey->x,
      .creator_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .creator_pub_key_ec_y = (unsigned char *)uds_pubkey->y,
      .creator_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
  };
  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_cert_tbs_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  dice_cert_key_id_pair_t *key_ids,
                                  attestation_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_cert_tbs_params = {
      .rom_ext_hash = (unsigned char *)rom_ext_measurement->digest,
      .rom_ext_hash_size = kDiceMeasurementSizeInBytes,
      .rom_ext_security_version = rom_ext_security_version,
      .owner_intermediate_pub_key_id = (unsigned char *)key_ids->cert->digest,
      .owner_intermediate_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
      .creator_pub_key_id = (unsigned char *)key_ids->endorsement->digest,
      .creator_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_ec_x = (unsigned char *)cdi_0_pubkey->x,
      .owner_intermediate_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .owner_intermediate_pub_key_ec_y = (unsigned char *)cdi_0_pubkey->y,
      .owner_intermediate_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
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
      kCdi0AttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      kCdi0KeymgrDiversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  dice_cert_key_id_pair_t *key_ids,
                                  attestation_public_key_t *cdi_1_pubkey,
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
      .owner_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_id =
          (unsigned char *)key_ids->endorsement->digest,
      .owner_intermediate_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
      .owner_pub_key_ec_x = (unsigned char *)cdi_1_pubkey->x,
      .owner_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .owner_pub_key_ec_y = (unsigned char *)cdi_1_pubkey->y,
      .owner_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
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
      kCdi1AttestationKeySeed, kOtbnBootAttestationKeyTypeDice,
      kCdi1KeymgrDiversifier));

  return kErrorOk;
}

rom_error_t dice_tpm_ek_cert_build(manuf_certgen_inputs_t *inputs,
                                   attestation_public_key_t *tpm_ek_pubkey,
                                   hmac_digest_t *digest, uint8_t *tpm_ek_tbs,
                                   size_t *tpm_ek_tbs_size) {
  tpm_ek_tbs_values_t tpm_ek_tbs_params = {
      .auth_key_key_id = inputs->auth_key_key_id,
      .auth_key_key_id_size = kDiceCertKeyIdSizeInBytes,
      .tpm_ek_pub_key_ec_x = (unsigned char *)tpm_ek_pubkey->x,
      .tpm_ek_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .tpm_ek_pub_key_ec_y = (unsigned char *)tpm_ek_pubkey->y,
      .tpm_ek_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
      .tpm_ek_pub_key_id = (unsigned char *)digest->digest,  // Nobody cares.
      .tpm_ek_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
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

rom_error_t dice_tpm_cek_cert_build(manuf_certgen_inputs_t *inputs,
                                    attestation_public_key_t *tpm_cek_pubkey,
                                    hmac_digest_t *digest, uint8_t *tpm_cek_tbs,
                                    size_t *tpm_cek_tbs_size) {
  tpm_cek_tbs_values_t tpm_cek_tbs_params = {
      .auth_key_key_id = inputs->auth_key_key_id,
      .auth_key_key_id_size = kDiceCertKeyIdSizeInBytes,
      .tpm_cek_pub_key_ec_x = (unsigned char *)tpm_cek_pubkey->x,
      .tpm_cek_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .tpm_cek_pub_key_ec_y = (unsigned char *)tpm_cek_pubkey->y,
      .tpm_cek_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
      .tpm_cek_pub_key_id = (unsigned char *)digest->digest,
      .tpm_cek_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
  };

  HARDENED_RETURN_IF_ERROR(
      tpm_cek_build_tbs(&tpm_cek_tbs_params, tpm_cek_tbs, tpm_cek_tbs_size));

  return kErrorOk;
}

rom_error_t dice_tpm_cik_cert_build(manuf_certgen_inputs_t *inputs,
                                    attestation_public_key_t *tpm_cik_pubkey,
                                    hmac_digest_t *digest, uint8_t *tpm_cik_tbs,
                                    size_t *tpm_cik_tbs_size) {
  tpm_cik_tbs_values_t tpm_cik_tbs_params = {
      .auth_key_key_id = inputs->auth_key_key_id,
      .auth_key_key_id_size = kDiceCertKeyIdSizeInBytes,
      .tpm_cik_pub_key_ec_x = (unsigned char *)tpm_cik_pubkey->x,
      .tpm_cik_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .tpm_cik_pub_key_ec_y = (unsigned char *)tpm_cik_pubkey->y,
      .tpm_cik_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
      .tpm_cik_pub_key_id = (unsigned char *)digest->digest,
      .tpm_cik_pub_key_id_size = kDiceCertKeyIdSizeInBytes,
  };

  HARDENED_RETURN_IF_ERROR(
      tpm_cik_build_tbs(&tpm_cik_tbs_params, tpm_cik_tbs, tpm_cik_tbs_size));

  return kErrorOk;
}
