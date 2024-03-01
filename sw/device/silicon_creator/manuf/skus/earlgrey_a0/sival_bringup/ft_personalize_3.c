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
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static_assert(kUdsMaxTbsSizeBytes == 569,
              "The `uds_tbs_certificate` buffer size in the "
              "`manuf_cert_perso_data_out_t` struct should match the value of "
              "`kUdsMaxTbsSizeBytes`.");
static_assert(kCdi0MaxCertSizeBytes == 582,
              "The `cdi_0_certificate` buffer size in the "
              "`manuf_cert_perso_data_out_t` struct should match the value of "
              "`kCdi0MaxCertSizeBytes`.");
static_assert(kCdi1MaxCertSizeBytes == 631,
              "The `cdi_1_certificate` buffer size in the "
              "`manuf_cert_perso_data_out_t` struct should match the value of "
              "`kCdi1MaxCertSizeBytes`.");

static manuf_cert_perso_data_in_t in_data;
hmac_digest_t uds_pubkey_id;
hmac_digest_t cdi_0_pubkey_id;
static manuf_cert_perso_data_out_t out_data = {
    .uds_tbs_certificate = {0},
    .uds_tbs_certificate_size = kUdsMaxTbsSizeBytes,
    .cdi_0_certificate = {0},
    .cdi_0_certificate_size = kCdi0MaxCertSizeBytes,
    .cdi_1_certificate = {0},
    .cdi_1_certificate_size = kCdi1MaxCertSizeBytes,
};
static manuf_endorsed_certs_t endorsed_certs;

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
 * Crank the keymgr to produce the attestation keys and certificates.
 */
static status_t personalize(ujson_t *uj) {
  // Retrieve certificate provisioning data.
  LOG_INFO("Waiting for FT provisioning data ...");
  TRY(ujson_deserialize_manuf_cert_perso_data_in_t(uj, &in_data));

  // Configure certificate flash info page permissions.
  TRY(config_certificate_flash_pages());

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to Initialized state.
  TRY(keymgr_state_check(kKeymgrStateReset));
  keymgr_advance_state();

  // Load OTBN attestation keygen program.
  TRY(otbn_boot_app_load());

  // Generate UDS keys and (TBS) cert.
  TRY(dice_uds_cert_build(&in_data, &uds_pubkey_id,
                          out_data.uds_tbs_certificate,
                          &out_data.uds_tbs_certificate_size));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageUdsCertificate,
      kFlashInfoFieldUdsCertificate.byte_offset,
      out_data.uds_tbs_certificate_size / sizeof(uint32_t),
      out_data.uds_tbs_certificate));
  LOG_INFO("Generated UDS certificate.");

  // Generate CDI_0 keys and cert.
  TRY(dice_cdi_0_cert_build(&in_data, &uds_pubkey_id, &cdi_0_pubkey_id,
                            out_data.cdi_0_certificate,
                            &out_data.cdi_0_certificate_size));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashInfoFieldCdi0Certificate.byte_offset,
                            out_data.cdi_0_certificate_size / sizeof(uint32_t),
                            out_data.cdi_0_certificate));
  LOG_INFO("Generated CDI_0 certificate.");

  // Generate CDI_1 keys and cert.
  TRY(dice_cdi_1_cert_build(&in_data, &cdi_0_pubkey_id,
                            out_data.cdi_1_certificate,
                            &out_data.cdi_1_certificate_size));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashInfoFieldCdi1Certificate.byte_offset,
                            out_data.cdi_1_certificate_size / sizeof(uint32_t),
                            out_data.cdi_1_certificate));
  LOG_INFO("Generated CDI_1 certificate.");

  // Export the certificates to the provisioning appliance.
  LOG_INFO("Exporting certificates ...");
  RESP_OK(ujson_serialize_manuf_cert_perso_data_out_t, uj, &out_data);

  // Import endorsed certificates from the provisioning appliance.
  LOG_INFO("Importing certificates ...");
  TRY(ujson_deserialize_manuf_endorsed_certs_t(uj, &endorsed_certs));

  // Write the endorsed UDS certificate to flash and ack to host.
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageUdsCertificate,
      kFlashInfoFieldUdsCertificate.byte_offset,
      endorsed_certs.uds_certificate_size / sizeof(uint32_t),
      endorsed_certs.uds_certificate));
  LOG_INFO("Imported UDS certificate.");

  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();

  CHECK_STATUS_OK(personalize(&uj));

  return true;
}
