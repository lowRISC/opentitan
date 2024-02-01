// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
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
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static_assert(kUdsMaxTbsSizeBytes == 712,
              "The `uds_tbs_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kUdsMaxTbsSizeBytes`.");
static_assert(kUdsMaxCertSizeBytes == 803,
              "The `uds_tbs_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kUdsMaxTbsSizeBytes`.");
static_assert(kCdi0MaxCertSizeBytes == 580,
              "The `cdi_0_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kCdi0MaxCertSizeBytes`.");
static_assert(kCdi1MaxCertSizeBytes == 629,
              "The `cdi_1_certificate` buffer size in the "
              "`manuf_dice_certs_t` struct should match the value of "
              "`kCdi1MaxCertSizeBytes`.");

/**
 * Peripheral handles.
 */
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * RMA unlock token wrapping data.
 */
static ecc_p256_public_key_t host_ecc_pk;
static wrapped_rma_unlock_token_t wrapped_rma_token;

/**
 * Keymgr binding values.
 */
static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};

/**
 * Certificate data.
 */
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
static manuf_certgen_inputs_t certgen_inputs;
static hmac_digest_t uds_pubkey_id;
static hmac_digest_t cdi_0_pubkey_id;
static hmac_digest_t cdi_1_pubkey_id;
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
 * Initializes all DIF handles used in this program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_rstmgr_init(mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR),
                      &rstmgr));
  return OK_STATUS();
}

/**
 * Issue a software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

/**
 * Configures flash info pages to store device certificates.
 */
static status_t config_and_erase_certificate_flash_pages(void) {
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
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

/**
 * Provision OTP SECRET{1,2} partitions, enable flash scrambling, and reboot.
 */
static status_t personalize_otp_secrets(ujson_t *uj) {
  // Provision OTP Secret1 partition, and complete provisioning of OTP
  // CreatorSwCfg partition.
  if (!status_ok(manuf_personalize_device_secret1_check(&otp_ctrl))) {
    TRY(manuf_personalize_device_secret1(&lc_ctrl, &otp_ctrl));
  }
  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_flash_data_default_cfg(&otp_ctrl));
    TRY(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
    LOG_INFO("Bootstrap requested.");
    wait_for_interrupt();
  }

  // Provision OTP Secret2 partition and keymgr flash info pages (1, 2, and 4).
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    LOG_INFO("Waiting for host public key ...");
    TRY(ujson_deserialize_ecc_p256_public_key_t(uj, &host_ecc_pk));
    TRY(manuf_personalize_device_secrets(&flash_ctrl_state, &lc_ctrl, &otp_ctrl,
                                         &host_ecc_pk, &wrapped_rma_token));
    LOG_INFO("Exporting RMA token ...");
    RESP_OK(ujson_serialize_wrapped_rma_unlock_token_t, uj, &wrapped_rma_token);
    sw_reset();
  }

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
 * Crank the keymgr to produce the DICE attestation keys and certificates.
 */
static status_t personalize_dice_certificates(ujson_t *uj) {
  // Retrieve certificate provisioning data.
  LOG_INFO("Waiting for DICE certificate inputs ...");
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, &certgen_inputs));

  // Configure certificate flash info page permissions.
  TRY(config_and_erase_certificate_flash_pages());

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to Initialized state.
  TRY(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  TRY(sc_keymgr_state_check(kScKeymgrStateInit));

  // Load OTBN attestation keygen program.
  // TODO(#21550): this should already be loaded by the ROM.
  TRY(otbn_boot_app_load());

  // Generate UDS keys and (TBS) cert.
  sc_keymgr_advance_state();
  TRY(dice_attestation_keygen(kDiceKeyUds, &uds_pubkey_id, &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kUdsKeymgrDiversifier));
  TRY(dice_uds_cert_build(&certgen_inputs, &uds_pubkey_id, &curr_pubkey,
                          dice_certs.uds_tbs_certificate,
                          &dice_certs.uds_tbs_certificate_size));
  LOG_INFO("Generated UDS TBS certificate.");

  // Generate CDI_0 keys and cert.
  compute_keymgr_owner_int_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_int_advance(&sealing_binding_value,
                                  &attestation_binding_value,
                                  /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi0, &cdi_0_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_0_cert_build(&certgen_inputs, &uds_pubkey_id, &cdi_0_pubkey_id,
                            &curr_pubkey, dice_certs.cdi_0_certificate,
                            &dice_certs.cdi_0_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi0Certificate,
      kFlashInfoFieldCdi0Certificate.byte_offset,
      dice_certs.cdi_0_certificate_size / sizeof(uint32_t),
      dice_certs.cdi_0_certificate));
  LOG_INFO("Generated CDI_0 certificate.");

  // Generate CDI_1 keys and cert.
  compute_keymgr_owner_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_advance(&sealing_binding_value,
                              &attestation_binding_value,
                              /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi1, &cdi_1_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_1_cert_build(&certgen_inputs, &cdi_0_pubkey_id, &cdi_1_pubkey_id,
                            &curr_pubkey, dice_certs.cdi_1_certificate,
                            &dice_certs.cdi_1_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi1Certificate,
      kFlashInfoFieldCdi1Certificate.byte_offset,
      dice_certs.cdi_1_certificate_size / sizeof(uint32_t),
      dice_certs.cdi_1_certificate));
  LOG_INFO("Generated CDI_1 certificate.");

  // Export the certificates to the provisioning appliance.
  LOG_INFO("Exporting DICE certificates ...");
  RESP_OK(ujson_serialize_manuf_dice_certs_t, uj, &dice_certs);

  // Import endorsed certificates from the provisioning appliance.
  LOG_INFO("Importing DICE UDS certificate ...");
  TRY(ujson_deserialize_manuf_endorsed_certs_t(uj, &endorsed_certs));

  // Write the endorsed UDS certificate to flash and ack to host.
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageUdsCertificate,
      kFlashInfoFieldUdsCertificate.byte_offset,
      endorsed_certs.uds_certificate_size / sizeof(uint32_t),
      endorsed_certs.uds_certificate));
  LOG_INFO("Imported DICE UDS certificate.");

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
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();
  log_self_hash();
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  CHECK_STATUS_OK(personalize_otp_secrets(&uj));
  CHECK_STATUS_OK(personalize_dice_certificates(&uj));
  return true;
}
