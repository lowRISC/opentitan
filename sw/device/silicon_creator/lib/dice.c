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
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"    // Generated.
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
static attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static attestation_public_key_t curr_pubkey_be = {.x = {0}, .y = {0}};
static attestation_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};
static attestation_signature_t curr_tbs_signature_be = {.r = {0}, .s = {0}};
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

static_assert(kAttestMeasurementSizeInBytes == 32,
              "The attestation measurement size should equal the size of the "
              "keymgr binding registers.");

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
 * Helper function to convert a buffer of bytes from little to big endian.
 */
static void le_be_buf_format(unsigned char *dst, unsigned char *src,
                             size_t num_bytes) {
  for (size_t i = 0; i < num_bytes; ++i) {
    dst[i] = src[num_bytes - i - 1];
  }
}

/**
 * Helper function to convert an attestation public from little to big endian.
 */
static void curr_pubkey_le_to_be_convert(void) {
  le_be_buf_format((unsigned char *)curr_pubkey_be.x,
                   (unsigned char *)curr_pubkey.x,
                   kAttestationPublicKeyCoordBytes);
  le_be_buf_format((unsigned char *)curr_pubkey_be.y,
                   (unsigned char *)curr_pubkey.y,
                   kAttestationPublicKeyCoordBytes);
}

/**
 * Helper function to convert an attestation certificate signature from little
 * to big endian.
 */
static void curr_tbs_signature_le_to_be_convert(void) {
  le_be_buf_format((unsigned char *)curr_tbs_signature_be.r,
                   (unsigned char *)curr_tbs_signature.r,
                   kAttestationSignatureBytes / 2);
  le_be_buf_format((unsigned char *)curr_tbs_signature_be.s,
                   (unsigned char *)curr_tbs_signature.s,
                   kAttestationSignatureBytes / 2);
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

rom_error_t dice_uds_cert_build(manuf_certgen_inputs_t *inputs,
                                hmac_digest_t *uds_pubkey_id, uint8_t *tbs_cert,
                                size_t *tbs_cert_size) {
  // Generate the UDS key.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, kUdsKeymgrDiversifier, &curr_pubkey));
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kUdsAttestationKeySeed, kUdsKeymgrDiversifier));
  curr_pubkey_le_to_be_convert();

  // Generate the key ID.
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2, uds_pubkey_id);

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
      .creator_pub_key_id = (unsigned char *)uds_pubkey_id->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .auth_key_key_id = inputs->auth_key_key_id,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_ec_x = (unsigned char *)curr_pubkey_be.x,
      .creator_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .creator_pub_key_ec_y = (unsigned char *)curr_pubkey_be.y,
      .creator_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
  };
  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_cert_tbs_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *uds_pubkey_id,
                                  hmac_digest_t *cdi_0_pubkey_id, uint8_t *cert,
                                  size_t *cert_size) {
  // Generate the CDI_0 key.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kCdi0AttestationKeySeed, kCdi0KeymgrDiversifier, &curr_pubkey));
  curr_pubkey_le_to_be_convert();

  // Generate the key ID.
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2,
              cdi_0_pubkey_id);

  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_cert_tbs_params = {
      .rom_ext_hash = (unsigned char *)inputs->rom_ext_measurement,
      .rom_ext_hash_size = kAttestMeasurementSizeInBytes,
      .rom_ext_security_version = inputs->rom_ext_security_version,
      .owner_intermediate_pub_key_id = (unsigned char *)cdi_0_pubkey_id->digest,
      .owner_intermediate_pub_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_id = (unsigned char *)uds_pubkey_id->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_ec_x = (unsigned char *)curr_pubkey_be.x,
      .owner_intermediate_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .owner_intermediate_pub_key_ec_y = (unsigned char *)curr_pubkey_be.y,
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
  curr_tbs_signature_le_to_be_convert();
  cdi_0_cert_params.cert_signature_r = (unsigned char *)curr_tbs_signature_be.r;
  cdi_0_cert_params.cert_signature_r_size = kAttestationSignatureBytes / 2;
  cdi_0_cert_params.cert_signature_s = (unsigned char *)curr_tbs_signature_be.s;
  cdi_0_cert_params.cert_signature_s_size = kAttestationSignatureBytes / 2;
  HARDENED_RETURN_IF_ERROR(
      cdi_0_build_cert(&cdi_0_cert_params, cert, cert_size));

  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kCdi0AttestationKeySeed, kCdi0KeymgrDiversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *cdi_0_pubkey_id, uint8_t *cert,
                                  size_t *cert_size) {
  // Generate the CDI_1 key.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kCdi1AttestationKeySeed, kCdi1KeymgrDiversifier, &curr_pubkey));
  curr_pubkey_le_to_be_convert();

  // Generate the key ID.
  hmac_digest_t cdi_1_pubkey_id;
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2,
              &cdi_1_pubkey_id);

  // Generate the TBS certificate.
  cdi_1_tbs_values_t cdi_1_cert_tbs_params = {
      .owner_hash = (unsigned char *)inputs->owner_measurement,
      .owner_hash_size = kAttestMeasurementSizeInBytes,
      .owner_manifest_hash =
          (unsigned char *)inputs->owner_manifest_measurement,
      .owner_manifest_hash_size = kAttestMeasurementSizeInBytes,
      .owner_security_version = inputs->owner_security_version,
      .owner_pub_key_id = (unsigned char *)cdi_1_pubkey_id.digest,
      .owner_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_id = (unsigned char *)cdi_0_pubkey_id->digest,
      .owner_intermediate_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_pub_key_ec_x = (unsigned char *)curr_pubkey_be.x,
      .owner_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .owner_pub_key_ec_y = (unsigned char *)curr_pubkey_be.y,
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
  curr_tbs_signature_le_to_be_convert();
  cdi_1_cert_params.cert_signature_r = (unsigned char *)curr_tbs_signature_be.r;
  cdi_1_cert_params.cert_signature_r_size = kAttestationSignatureBytes / 2;
  cdi_1_cert_params.cert_signature_s = (unsigned char *)curr_tbs_signature_be.s;
  cdi_1_cert_params.cert_signature_s_size = kAttestationSignatureBytes / 2;
  HARDENED_RETURN_IF_ERROR(
      cdi_1_build_cert(&cdi_1_cert_params, cert, cert_size));

  // Save the CDI_1 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kCdi1AttestationKeySeed, kCdi1KeymgrDiversifier));

  return kErrorOk;
}
