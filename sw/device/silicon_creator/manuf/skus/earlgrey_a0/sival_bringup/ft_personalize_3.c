// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"    // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  /**
   * Attestation measurement sizes, comprised of a SHA256 digest.
   */
  kAttestMeasurementSizeInBits = 256,
  kAttestMeasurementSizeInBytes = kAttestMeasurementSizeInBits / 8,
  kAttestMeasurementSizeIn32BitWords =
      kAttestMeasurementSizeInBytes / sizeof(uint32_t),

  /**
   * Certificate Key ID size.
   */
  kCertKeyIdSizeInBytes = 20,
};

static manuf_cert_perso_data_in_t in_data;
static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};
static uint32_t rom_ext_measurements[kAttestMeasurementSizeIn32BitWords * 2];

// Certificate data.
static attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static manuf_cert_perso_data_out_t out_data = {
    .uds_certificate = {0},
    .uds_certificate_size = kUdsMaxCertSizeBytes,
    .cdi_0_certificate = {0},
    .cdi_0_certificate_size = kCdi0MaxCertSizeBytes,
};
// UDS.
hmac_digest_t uds_pubkey_id;
static uint8_t uds_tbs_buffer[kUdsMaxTbsSizeBytes];
static uds_sig_values_t uds_cert_params = {
    .tbs = uds_tbs_buffer,
    .tbs_size = kUdsMaxTbsSizeBytes,
};
// CDI_0.
hmac_digest_t cdi_0_pubkey_id;
static uint8_t cdi_0_tbs_buffer[kCdi0MaxTbsSizeBytes];
static cdi_0_sig_values_t cdi_0_cert_params = {
    .tbs = cdi_0_tbs_buffer,
    .tbs_size = kCdi0MaxTbsSizeBytes,
};

static const flash_ctrl_perms_t kCertificateFlashInfoPerms = {
    .read = kMultiBitBool4True,
    .write = kMultiBitBool4True,
    .erase = kMultiBitBool4True,
};

static const flash_ctrl_cfg_t kCertificateFlashInfoCfg = {
    .scrambling = kMultiBitBool4True,
    .ecc = kMultiBitBool4True,
    .he = kMultiBitBool4False,
};

static status_t config_certificate_flash_pages(void) {
  const flash_ctrl_info_page_t *kCertFlashInfoPages[] = {
      &kFlashCtrlInfoPageUdsCertificate,
      &kFlashCtrlInfoPageCdi0Certificate,
      &kFlashCtrlInfoPageCdi1Certificate,
  };
  for (size_t i = 0; i < ARRAYSIZE(kCertFlashInfoPages); ++i) {
    flash_ctrl_info_cfg_set(kCertFlashInfoPages[i], kCertificateFlashInfoCfg);
    flash_ctrl_info_perms_set(kCertFlashInfoPages[i],
                              kCertificateFlashInfoPerms);
  }
  return OK_STATUS();
}

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
 * Generates the UDS attestation keypair and (unendorsed) X.509 certificate.
 *
 * Preconditions: keymgr has been initialized, and is ready to be cranked.
 *
 * @param[in,out] pubkey_id Pointer the generated UDS public key ID.
 * @param[out] cert Buffer to hold the generated UDS certificate.
 * @param[in,out] cert_size Size of the UDS certificate (input value is the size
 *                          of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
static status_t gen_uds_keys_and_cert(hmac_digest_t *pubkey_id, uint8_t *cert,
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
  hmac_sha256(&curr_pubkey, kAttestationPublicKeyCoordBytes * 2, pubkey_id);

  // Generate the (unendorsed) certificate.
  uds_tbs_values_t uds_cert_tbs_params = {
      // TODO(#19455): include OTP measurements in attestation keygen / cert.
      .otp_creator_sw_cfg_hash = NULL,
      .otp_creator_sw_cfg_hash_size = 0,
      .otp_owner_sw_cfg_hash = NULL,
      .otp_owner_sw_cfg_hash_size = 0,
      .otp_hw_cfg0_hash = NULL,
      .otp_hw_cfg0_hash_size = 0,
      .debug_flag = is_debug_exposed(),
      .creator_pub_key_id = (unsigned char *)pubkey_id->digest,
      .creator_pub_key_id_size = kCertKeyIdSizeInBytes,
      .auth_key_key_id = in_data.auth_key_key_id,
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

/**
 * Generates the CDI_0 attestation keypair and X.509 certificate.
 *
 * Preconditions: keymgr has cranked to the `CreatorRootKey` stage.
 *
 * @param uds_pubkey_id Pointer the generated UDS public key ID.
 * @param[in,out] cdi_0_pubkey_id Pointer the generated CDI_0 public key ID.
 * @param[out] cert Buffer to hold the generated CDI_0 certificate.
 * @param[in,out] cert_size Size of the CDI_0 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
static status_t gen_cdi_0_keys_and_cert(hmac_digest_t *uds_pubkey_id,
                                        hmac_digest_t *cdi_0_pubkey_id,
                                        uint8_t *cert, size_t *cert_size) {
  // Set attestation binding to the ROM_EXT / Ownership Manifest measurements.
  // We set the sealing binding value to all zeros as it is unused in the
  // current personalization flow. This may be changed in the future.
  TRY(keymgr_state_check(kKeymgrStateCreatorRootKey));
  hmac_digest_t combined_measurements;
  memcpy(rom_ext_measurements, in_data.rom_ext_measurement,
         kAttestMeasurementSizeInBytes);
  memcpy(&rom_ext_measurements[kAttestMeasurementSizeIn32BitWords],
         in_data.owner_manifest_measurement, kAttestMeasurementSizeInBytes);
  hmac_sha256(rom_ext_measurements, kAttestMeasurementSizeInBytes * 2,
              &combined_measurements);
  memcpy(attestation_binding_value.data, combined_measurements.digest,
         kAttestMeasurementSizeInBytes);
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
      .rom_ext_hash = (unsigned char *)in_data.rom_ext_measurement,
      .rom_ext_hash_size = kAttestMeasurementSizeInBytes,
      .owner_manifest_hash =
          (unsigned char *)in_data.owner_manifest_measurement,
      .owner_manifest_hash_size = kAttestMeasurementSizeInBytes,
      .rom_ext_security_version = in_data.rom_ext_security_version,
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

/**
 * Crank the keymgr to produce the attestation keys and certificates.
 */
static status_t personalize(ujson_t *uj) {
  // Retrieve certificate provisioning data.
  LOG_INFO("Waiting for FT provisioning data ...");
  TRY(ujson_deserialize_manuf_cert_perso_data_in_t(uj, &in_data));

  // Configure certificate flash info page permissions.
  TRY(config_certificate_flash_pages());

  // Advance keymgr to Initialized state.
  TRY(entropy_complex_init());
  // Initialize KMAC for key manager operations.
  TRY(kmac_keymgr_configure());
  TRY(keymgr_state_check(kKeymgrStateReset));
  keymgr_advance_state();

  // Load OTBN attestation keygen program.
  TRY(otbn_boot_app_load());

  // Generate UDS keys and cert.
  TRY(gen_uds_keys_and_cert(&uds_pubkey_id, out_data.uds_certificate,
                            &out_data.uds_certificate_size));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashInfoFieldUdsCertificate.byte_offset,
                            out_data.uds_certificate_size / sizeof(uint32_t),
                            out_data.uds_certificate));
  LOG_INFO("Generated UDS certificate.");

  // Generate CDI_0 keys and cert.
  TRY(gen_cdi_0_keys_and_cert(&uds_pubkey_id, &cdi_0_pubkey_id,
                              out_data.cdi_0_certificate,
                              &out_data.cdi_0_certificate_size));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashInfoFieldCdi0Certificate.byte_offset,
                            out_data.cdi_0_certificate_size / sizeof(uint32_t),
                            out_data.cdi_0_certificate));
  LOG_INFO("Generated CDI_0 certificate.");

  // Set attestation binding to OWNER measurement.
  // We keep the sealing binding value to all zeros as it is unused in the
  // current personalization flow. This may be changed in the future.
  memcpy(attestation_binding_value.data, in_data.owner_measurement,
         kAttestMeasurementSizeInBytes);
  keymgr_sw_binding_unlock_wait();
  keymgr_sw_binding_set(&sealing_binding_value, &attestation_binding_value);

  // Advance keymgr and generate CDI_1 attestation keys / cert.
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateOwnerKey));
  TRY(otbn_boot_attestation_keygen(kCdi1AttestationKeySeed,
                                   kCdi1KeymgrDiversifier, &curr_pubkey));
  // TODO(#19455): create certificate with key, endorse it, and write it to
  // flash info.
  //
  // Until then, we just write the public key to flash and export it over the
  // console.
  memcpy(out_data.cdi_1_certificate.x, curr_pubkey.x,
         kAttestationPublicKeyCoordBytes);
  memcpy(out_data.cdi_1_certificate.y, curr_pubkey.y,
         kAttestationPublicKeyCoordBytes);
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashInfoFieldCdi1Certificate.byte_offset,
                            sizeof(attestation_public_key_t) / sizeof(uint32_t),
                            &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kCdi1AttestationKeySeed,
                                     kCdi1KeymgrDiversifier));

  LOG_INFO("Exporting attestation certificates ...");
  RESP_OK(ujson_serialize_manuf_cert_perso_data_out_t, uj, &out_data);

  LOG_INFO("Wait for UDS attestation certificate endorsement ...");
  // TODO(#19455): update UDS certificate signature field and commit to flash.

  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();

  CHECK_STATUS_OK(personalize(&uj));

  return true;
}
