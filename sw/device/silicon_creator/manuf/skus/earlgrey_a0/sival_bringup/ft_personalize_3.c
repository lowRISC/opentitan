// Copyright lowRISC contributors (OpenTitan project).
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
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"    // Generated.
#include "sw/device/silicon_creator/lib/dice.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static_assert(kUdsMaxTbsSizeBytes == 567,
              "The `uds_tbs_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kUdsMaxTbsSizeBytes`.");
static_assert(kUdsMaxCertSizeBytes == 658,
              "The `uds_certificate` buffer size in the "
              "`manuf_endorsed_certs_t` struct should match the value of "
              "`kUdsMaxSizeBytes`.");
static_assert(kCdi0MaxCertSizeBytes == 580,
              "The `cdi_0_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kCdi0MaxCertSizeBytes`.");
static_assert(kCdi1MaxCertSizeBytes == 629,
              "The `cdi_1_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kCdi1MaxCertSizeBytes`.");

/**
 * Certificate data.
 */
static manuf_certgen_inputs_t certgen_inputs;
static hmac_digest_t uds_endorsement_key_id;
static hmac_digest_t uds_pubkey_id;
static hmac_digest_t cdi_0_pubkey_id;
static hmac_digest_t cdi_1_pubkey_id;
static dice_cert_key_id_pair_t uds_key_ids = {
    .endorsement = &uds_endorsement_key_id,
    .cert = &uds_pubkey_id,
};
static dice_cert_key_id_pair_t cdi_0_key_ids = {
    .endorsement = &uds_pubkey_id,
    .cert = &cdi_0_pubkey_id,
};
static dice_cert_key_id_pair_t cdi_1_key_ids = {
    .endorsement = &cdi_0_pubkey_id,
    .cert = &cdi_1_pubkey_id,
};
static attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static manuf_dice_certs_t dice_certs = {
    .uds_tbs_certificate = {0},
    .uds_tbs_certificate_size = kUdsMaxTbsSizeBytes,
    .cdi_0_certificate = {0},
    .cdi_0_certificate_size = kCdi0MaxCertSizeBytes,
    .cdi_1_certificate = {0},
    .cdi_1_certificate_size = kCdi1MaxCertSizeBytes,
};
static manuf_endorsed_certs_t endorsed_certs;

/**
 * Keymgr binding values.
 */
static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};

/**
 * Configures flash info pages to store device certificates.
 */
static status_t config_and_erase_certificate_flash_pages(void) {
  flash_ctrl_cert_info_pages_creator_cfg();
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

/**
 * Sets the attestation binding to the ROM_EXT measurement, and the sealing
 * binding to all zeros.
 *
 * The sealing binding value is set to all zeros as it is unused in the current
 * personalization flow. This may be changed in the future.
 */
static void compute_keymgr_owner_int_binding(manuf_certgen_inputs_t *inputs) {
  memcpy(attestation_binding_value.data, inputs->rom_ext_measurement,
         kDiceMeasurementSizeInBytes);
  memset(sealing_binding_value.data, 0, kDiceMeasurementSizeInBytes);
}

/**
 * Sets the attestation binding to a combination of the Owner firmware and
 * Ownership Manifest measurements, and the sealing binding to all zeros.
 *
 * The sealing binding value is set to all zeros as it is unused in the current
 * personalization flow. This may be changed in the future.
 */
static void compute_keymgr_owner_binding(manuf_certgen_inputs_t *inputs) {
  hmac_digest_t combined_measurements;
  hmac_sha256_init();
  hmac_sha256_update((unsigned char *)inputs->owner_measurement,
                     kDiceMeasurementSizeInBytes);
  hmac_sha256_update((unsigned char *)inputs->owner_manifest_measurement,
                     kDiceMeasurementSizeInBytes);
  memcpy(attestation_binding_value.data, combined_measurements.digest,
         kDiceMeasurementSizeInBytes);
  memset(sealing_binding_value.data, 0, kDiceMeasurementSizeInBytes);
}

/**
 * Crank the keymgr to produce the attestation keys and certificates.
 */
static status_t personalize(ujson_t *uj) {
  // Retrieve certificate provisioning data.
  LOG_INFO("Waiting for DICE certificate inputs ...");
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, &certgen_inputs));

  // Configure certificate flash info page permissions.
  TRY(config_and_erase_certificate_flash_pages());

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to Initialized state.
  TRY(keymgr_state_check(kKeymgrStateReset));
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateInit));

  // Load OTBN attestation keygen program.
  TRY(otbn_boot_app_load());

  // Generate UDS keys and (TBS) cert.
  keymgr_advance_state();
  TRY(dice_attestation_keygen(kDiceKeyUds, &uds_pubkey_id, &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kUdsKeymgrDiversifier));
  // We copy over the UDS endorsement key ID to an SHA256 digest type, since
  // this is the format of key IDs generated on-dice.
  memcpy(uds_endorsement_key_id.digest, certgen_inputs.auth_key_key_id,
         kDiceCertKeyIdSizeInBytes);
  TRY(dice_uds_tbs_cert_build(&uds_key_ids, &curr_pubkey,
                              dice_certs.uds_tbs_certificate,
                              &dice_certs.uds_tbs_certificate_size));

  LOG_INFO("Generated UDS TBS certificate.");

  // Generate CDI_0 keys and cert.
  compute_keymgr_owner_int_binding(&certgen_inputs);
  TRY(keymgr_owner_int_advance(&sealing_binding_value,
                               &attestation_binding_value,
                               /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi0, &cdi_0_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_0_cert_build(
      (hmac_digest_t *)certgen_inputs.rom_ext_measurement,
      certgen_inputs.rom_ext_security_version, &cdi_0_key_ids, &curr_pubkey,
      dice_certs.cdi_0_certificate, &dice_certs.cdi_0_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi0Certificate,
      /*offset=*/0, dice_certs.cdi_0_certificate_size / sizeof(uint32_t),
      dice_certs.cdi_0_certificate));
  LOG_INFO("Generated CDI_0 certificate.");

  // Generate CDI_1 keys and cert.
  compute_keymgr_owner_binding(&certgen_inputs);
  TRY(keymgr_owner_advance(&sealing_binding_value, &attestation_binding_value,
                           /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi1, &cdi_1_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_1_cert_build(
      (hmac_digest_t *)certgen_inputs.owner_measurement,
      (hmac_digest_t *)certgen_inputs.owner_manifest_measurement,
      certgen_inputs.owner_security_version, &cdi_1_key_ids, &curr_pubkey,
      dice_certs.cdi_1_certificate, &dice_certs.cdi_1_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi1Certificate,
      /*offset=*/0, dice_certs.cdi_1_certificate_size / sizeof(uint32_t),
      dice_certs.cdi_1_certificate));
  LOG_INFO("Generated CDI_1 certificate.");

  // Export the certificates to the provisioning appliance.
  LOG_INFO("Exporting DICE certificates ...");
  RESP_OK(ujson_serialize_manuf_dice_certs_t, uj, &dice_certs);

  // Import endorsed certificates from the provisioning appliance.
  LOG_INFO("Importing certificates ...");
  TRY(ujson_deserialize_manuf_endorsed_certs_t(uj, &endorsed_certs));

  // Write the endorsed UDS certificate to flash and ack to host.
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageUdsCertificate,
      /*offset=*/0, endorsed_certs.uds_certificate_size / sizeof(uint32_t),
      endorsed_certs.uds_certificate));
  LOG_INFO("Imported UDS certificate.");

  return OK_STATUS();
}

static void log_self_hash(void) {
  // clang-format off
  LOG_INFO("Personalization Firmware Hash: 0x%08x%08x%08x%08x%08x%08x%08x%08x",
           boot_measurements.rom_ext.data[7],
           boot_measurements.rom_ext.data[6],
           boot_measurements.rom_ext.data[5],
           boot_measurements.rom_ext.data[4],
           boot_measurements.rom_ext.data[3],
           boot_measurements.rom_ext.data[2],
           boot_measurements.rom_ext.data[1],
           boot_measurements.rom_ext.data[0]);
  // clang-format on
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();

  log_self_hash();
  CHECK_STATUS_OK(personalize(&uj));

  return true;
}
