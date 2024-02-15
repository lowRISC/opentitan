// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"    // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};
static attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static uint8_t uds_tbs_buffer[kUdsMaxTbsSizeBytes];
static uds_sig_values_t uds_cert_params = {
    .tbs = uds_tbs_buffer,
    .tbs_size = kUdsMaxTbsSizeBytes,
};
static uint8_t cdi_0_tbs_buffer[kCdi0MaxTbsSizeBytes];
static cdi_0_sig_values_t cdi_0_cert_params = {
    .tbs = cdi_0_tbs_buffer,
    .tbs_size = kCdi0MaxTbsSizeBytes,
};

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

status_t gen_uds_keys_and_cert(manuf_cert_perso_data_in_t *perso_data_in,
                               hmac_digest_t *uds_pubkey_id, uint8_t *cert,
                               size_t *cert_size) {
  // Generate the UDS key.
  TRY(keymgr_state_check(kKeymgrStateInit));
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateCreatorRootKey));
  TRY(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                   kUdsKeymgrDiversifier, &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kUdsKeymgrDiversifier));

  // Generate the key ID.
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2, uds_pubkey_id);

  // Generate the (unendorsed) certificate.
  uds_tbs_values_t uds_cert_tbs_params = {
      // TODO(#19455): include OTP measurements in attestation keygen / cert.
      .otp_creator_sw_cfg_hash = NULL,
      .otp_creator_sw_cfg_hash_size = 0,
      .otp_owner_sw_cfg_hash = NULL,
      .otp_owner_sw_cfg_hash_size = 0,
      .otp_hw_cfg_hash = NULL,
      .otp_hw_cfg_hash_size = 0,
      .debug_flag = is_debug_exposed(),
      .creator_pub_key_id = (unsigned char *)uds_pubkey_id->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .auth_key_key_id = perso_data_in->auth_key_key_id,
      .auth_key_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_ec_x = (unsigned char *)curr_pubkey.x,
      .creator_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .creator_pub_key_ec_y = (unsigned char *)curr_pubkey.y,
      .creator_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
  };
  TRY(uds_build_tbs(&uds_cert_tbs_params, uds_cert_params.tbs,
                    &uds_cert_params.tbs_size));
  TRY(uds_build_cert(&uds_cert_params, cert, cert_size));

  return OK_STATUS();
}

status_t gen_cdi_0_keys_and_cert(manuf_cert_perso_data_in_t *perso_data_in,
                                 hmac_digest_t *uds_pubkey_id,
                                 hmac_digest_t *cdi_0_pubkey_id, uint8_t *cert,
                                 size_t *cert_size) {
  TRY(keymgr_state_check(kKeymgrStateCreatorRootKey));

  // Set attestation binding to the ROM_EXT / Ownership Manifest measurements.
  hmac_digest_t combined_measurements;
  uint32_t rom_ext_measurements[kAttestMeasurementSizeIn32BitWords * 2];
  memcpy(rom_ext_measurements, perso_data_in->rom_ext_measurement,
         kAttestMeasurementSizeInBytes);
  memcpy(&rom_ext_measurements[kAttestMeasurementSizeIn32BitWords],
         perso_data_in->owner_manifest_measurement,
         kAttestMeasurementSizeInBytes);
  hmac_sha256(rom_ext_measurements, kAttestMeasurementSizeInBytes * 2,
              &combined_measurements);
  memcpy(attestation_binding_value.data, combined_measurements.digest,
         kAttestMeasurementSizeInBytes);
  // We set the sealing binding value to all zeros as it is unused in the
  // current personalization flow. This may be changed in the future.
  memset(sealing_binding_value.data, 0, kAttestMeasurementSizeInBytes);
  keymgr_sw_binding_unlock_wait();
  keymgr_sw_binding_set(&sealing_binding_value, &attestation_binding_value);

  // Generate the CDI_0 key.
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateOwnerIntermediateKey));
  TRY(otbn_boot_attestation_keygen(kCdi0AttestationKeySeed,
                                   kCdi0KeymgrDiversifier, &curr_pubkey));

  // Generate the key ID.
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2,
              cdi_0_pubkey_id);

  // Generate the TBS certificate.
  cdi_0_tbs_values_t cdi_0_cert_tbs_params = {
      .rom_ext_hash = (unsigned char *)perso_data_in->rom_ext_measurement,
      .rom_ext_hash_size = kAttestMeasurementSizeInBytes,
      .owner_manifest_hash =
          (unsigned char *)perso_data_in->owner_manifest_measurement,
      .owner_manifest_hash_size = kAttestMeasurementSizeInBytes,
      .rom_ext_security_version = perso_data_in->rom_ext_security_version,
      .owner_intermediate_pub_key_id = (unsigned char *)cdi_0_pubkey_id->digest,
      .owner_intermediate_pub_key_id_size = kCertKeyIdSizeInBytes,
      .creator_pub_key_id = (unsigned char *)uds_pubkey_id->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .owner_intermediate_pub_key_ec_x = (unsigned char *)curr_pubkey.x,
      .owner_intermediate_pub_key_ec_x_size = kAttestationPublicKeyCoordBytes,
      .owner_intermediate_pub_key_ec_y = (unsigned char *)curr_pubkey.y,
      .owner_intermediate_pub_key_ec_y_size = kAttestationPublicKeyCoordBytes,
  };
  TRY(cdi_0_build_tbs(&cdi_0_cert_tbs_params, cdi_0_cert_params.tbs,
                      &cdi_0_cert_params.tbs_size));

  // Sign the TBS and generate the certificate.
  hmac_digest_t tbs_digest;
  hmac_sha256(cdi_0_cert_params.tbs, cdi_0_cert_params.tbs_size, &tbs_digest);
  attestation_signature_t tbs_signature;
  TRY(otbn_boot_attestation_endorse(&tbs_digest, &tbs_signature));
  cdi_0_cert_params.cert_signature_r = (unsigned char *)tbs_signature.r;
  cdi_0_cert_params.cert_signature_r_size = kAttestationSignatureBytes / 2;
  cdi_0_cert_params.cert_signature_s = (unsigned char *)tbs_signature.s;
  cdi_0_cert_params.cert_signature_s_size = kAttestationSignatureBytes / 2;
  TRY(cdi_0_build_cert(&cdi_0_cert_params, cert, cert_size));

  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  TRY(otbn_boot_attestation_key_save(kCdi0AttestationKeySeed,
                                     kCdi0KeymgrDiversifier));

  return OK_STATUS();
}
