// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
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
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"    // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"    // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
#include "sw/device/silicon_creator/lib/cert/uds.h"      // Generated.
#include "sw/device/silicon_creator/lib/dice.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/ip_autogen/flash_ctrl/data/flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

// Check TBS certificate buffer sizes.
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, uds_tbs_certificate,
                              OT_ALIGN_MEM(kUdsMaxTbsSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, tpm_ek_tbs_certificate,
                              OT_ALIGN_MEM(kTpmEkMaxTbsSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, tpm_cek_tbs_certificate,
                              OT_ALIGN_MEM(kTpmCekMaxTbsSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, tpm_cik_tbs_certificate,
                              OT_ALIGN_MEM(kTpmCikMaxTbsSizeBytes));

// Check endorsed certificate buffer sizes.
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_certs_t, uds_certificate,
                              OT_ALIGN_MEM(kUdsMaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, cdi_0_certificate,
                              OT_ALIGN_MEM(kCdi0MaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_certs_t, cdi_1_certificate,
                              OT_ALIGN_MEM(kCdi1MaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_certs_t, tpm_ek_certificate,
                              OT_ALIGN_MEM(kTpmEkMaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_certs_t, tpm_cek_certificate,
                              OT_ALIGN_MEM(kTpmCekMaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_certs_t, tpm_cik_certificate,
                              OT_ALIGN_MEM(kTpmCikMaxCertSizeBytes));

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
static hmac_digest_t tpm_endorsement_key_id;
static hmac_digest_t tpm_pubkey_id;
static dice_cert_key_id_pair_t tpm_key_ids = {
    .endorsement = &tpm_endorsement_key_id, .cert = &tpm_pubkey_id};
static ecdsa_p256_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static manuf_certs_t tbs_certs = {
    .uds_tbs_certificate = {0},
    .uds_tbs_certificate_size = kUdsMaxTbsSizeBytes,
    .cdi_0_certificate = {0},
    .cdi_0_certificate_size = kCdi0MaxCertSizeBytes,
    .cdi_1_certificate = {0},
    .cdi_1_certificate_size = kCdi1MaxCertSizeBytes,
    .tpm_ek_tbs_certificate = {0},
    .tpm_ek_tbs_certificate_size = kTpmEkMaxTbsSizeBytes,
    .tpm_cek_tbs_certificate = {0},
    .tpm_cek_tbs_certificate_size = kTpmCekMaxTbsSizeBytes,
    .tpm_cik_tbs_certificate = {0},
    .tpm_cik_tbs_certificate_size = kTpmCikMaxTbsSizeBytes,
};
static manuf_endorsed_certs_t endorsed_certs;
static const unsigned char *kEndorsedTpmCerts[] = {
    endorsed_certs.tpm_ek_certificate,
    endorsed_certs.tpm_cek_certificate,
    endorsed_certs.tpm_cik_certificate,
};

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
  flash_ctrl_cert_info_pages_creator_cfg();
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageUdsCertificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi0Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageCdi1Certificate,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageTpmCerts,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

/**
 * Provision OTP SECRET{1,2} partitions, keymgr flash info pages, enable flash
 * scrambling, and reboot.
 */
static status_t personalize_otp_and_flash_secrets(ujson_t *uj) {
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
 *  A helper function to round up the passed in value to get it aligned to the
 *  requested number of bits.
 */
static uint32_t round_up_to(uint32_t input, uint32_t align_bits) {
  uint32_t mask = (1 << align_bits) - 1;

  return (input + mask) & ~mask;
}

/**
 * Calculate the number of 32-bit words necessary to fit the input number bytes.
 */
static uint32_t size_to_words(uint32_t bytes) {
  return round_up_to(bytes, 2) / sizeof(uint32_t);
}

/**
 * Retrieve the certificate size from the passed in pointer to its ASN1 header.
 * Perform some basic sanity checks.
 */
static uint32_t get_cert_size(const uint8_t *header) {
  if (header[0] != 0x30 || header[1] != 0x82) {
    return 0;
  }

  return (((uint32_t)header[2]) << 8) + header[3] + 4 /* size of the header */;
}

/**
 * Read a certificate from the passed in location in a flash INFO page and hash
 * its contents on the existing sha256 hashing stream. Determine the actual
 * certificate size from its ASN1 header.
 *
 * If the caller passed a pointer, save there the certificate size.
 */
static status_t hash_certificate(const flash_ctrl_info_page_t *page,
                                 size_t offset, size_t *size) {
  uint8_t buffer[1024];  // 1K should be enough for the largest certificate.
  uint32_t cert_size;
  uint32_t bytes_read;

  // Read the first word of the certificate which contains it's size.
  TRY(flash_ctrl_info_read(page, offset, 1, buffer));
  bytes_read = sizeof(uint32_t);
  cert_size = get_cert_size(buffer);
  if (cert_size == 0) {
    LOG_ERROR("Inconsistent certificate header %02x %02x page %x:%x", buffer[0],
              buffer[1], page->base_addr, offset);
    return DATA_LOSS();
  }
  if (cert_size > sizeof(buffer)) {
    LOG_ERROR("Bad certificate size %d page %x:%x", cert_size, page->base_addr,
              offset);
    return DATA_LOSS();
  }
  if ((cert_size + offset) > FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
    LOG_ERROR("Cert size overflow (%d + %d) page %x:%x", cert_size, offset,
              page->base_addr, offset);
    return DATA_LOSS();
  }

  offset += bytes_read;
  TRY(flash_ctrl_info_read(page, offset, size_to_words(cert_size - bytes_read),
                           buffer + bytes_read));
  hmac_sha256_update(buffer, cert_size);

  if (size) {
    *size = cert_size;
  }
  return OK_STATUS();
}

static status_t log_hash_of_all_certs(ujson_t *uj) {
  uint32_t cert_size;
  uint32_t page_offset = 0;
  serdes_sha256_hash_t hash;
  hmac_sha256_init();

  // Push DICE certificates into the hash (each resides on a separate page).
  TRY(hash_certificate(&kFlashCtrlInfoPageUdsCertificate, 0, NULL));
  TRY(hash_certificate(&kFlashCtrlInfoPageCdi0Certificate, 0, NULL));
  TRY(hash_certificate(&kFlashCtrlInfoPageCdi1Certificate, 0, NULL));

  // Push TPM certificates into the hash (all reside on the same page).
  for (size_t i = 0; i < ARRAYSIZE(kEndorsedTpmCerts); i++) {
    TRY(hash_certificate(&kFlashCtrlInfoPageTpmCerts, page_offset, &cert_size));
    page_offset += size_to_words(cert_size) * sizeof(uint32_t);
    page_offset = round_up_to(page_offset, 3);
  }

  // Log the final hash of all certificates to the host and console.
  hmac_sha256_final((hmac_digest_t *)&hash);
  RESP_OK(ujson_serialize_serdes_sha256_hash_t, uj, &hash);
  LOG_INFO("SHA256 hash of all certificates: %08x%08x%08x%08x%08x%08x%08x%08x",
           hash.data[7], hash.data[6], hash.data[5], hash.data[4], hash.data[3],
           hash.data[2], hash.data[1], hash.data[0]);

  return OK_STATUS();
}

/**
 * Crank the keymgr to produce the DICE attestation keys and certificates.
 */
static status_t personalize_dice_certificates(ujson_t *uj) {
  /*****************************************************************************
   * Initialization.
   ****************************************************************************/
  // Load OTBN attestation keygen program.
  // TODO(#21550): this should already be loaded by the ROM.
  TRY(otbn_boot_app_load());

  // Configure certificate flash info page permissions.
  TRY(config_and_erase_certificate_flash_pages());

  // Retrieve certificate provisioning data.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Waiting for certificate inputs ...");
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, &certgen_inputs));
  // We copy over the TPM/UDS endorsement key ID to an SHA256 digest type, since
  // this is the format of key IDs generated on-dice.
  memcpy(uds_endorsement_key_id.digest, certgen_inputs.auth_key_key_id,
         kDiceCertKeyIdSizeInBytes);
  memcpy(tpm_endorsement_key_id.digest, certgen_inputs.auth_key_key_id,
         kDiceCertKeyIdSizeInBytes);

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to CreatorRootKey state.
  TRY(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  TRY(sc_keymgr_state_check(kScKeymgrStateInit));
  sc_keymgr_advance_state();

  /*****************************************************************************
   * DICE certificates.
   ****************************************************************************/
  // Generate UDS keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyUds, &uds_pubkey_id, &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kOtbnBootAttestationKeyTypeDice,
                                     kUdsKeymgrDiversifier));
  TRY(dice_uds_tbs_cert_build(&uds_key_ids, &curr_pubkey,
                              tbs_certs.uds_tbs_certificate,
                              &tbs_certs.uds_tbs_certificate_size));
  LOG_INFO("Generated UDS TBS certificate.");

  // Generate CDI_0 keys and cert.
  compute_keymgr_owner_int_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_int_advance(&sealing_binding_value,
                                  &attestation_binding_value,
                                  /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi0, &cdi_0_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_0_cert_build(
      (hmac_digest_t *)certgen_inputs.rom_ext_measurement,
      certgen_inputs.rom_ext_security_version, &cdi_0_key_ids, &curr_pubkey,
      tbs_certs.cdi_0_certificate, &tbs_certs.cdi_0_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi0Certificate,
      /*offset=*/0, size_to_words(get_cert_size(tbs_certs.cdi_0_certificate)),
      tbs_certs.cdi_0_certificate));
  LOG_INFO("Generated CDI_0 certificate.");

  // Generate CDI_1 keys and cert.
  compute_keymgr_owner_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_advance(&sealing_binding_value,
                              &attestation_binding_value,
                              /*max_key_version=*/0));
  TRY(dice_attestation_keygen(kDiceKeyCdi1, &cdi_1_pubkey_id, &curr_pubkey));
  TRY(dice_cdi_1_cert_build(
      (hmac_digest_t *)certgen_inputs.owner_measurement,
      (hmac_digest_t *)certgen_inputs.owner_manifest_measurement,
      certgen_inputs.owner_security_version, &cdi_1_key_ids, &curr_pubkey,
      tbs_certs.cdi_1_certificate, &tbs_certs.cdi_1_certificate_size));
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageCdi1Certificate,
      /*offset=*/0, size_to_words(get_cert_size(tbs_certs.cdi_1_certificate)),
      tbs_certs.cdi_1_certificate));
  LOG_INFO("Generated CDI_1 certificate.");

  /*****************************************************************************
   * TPM certificates.
   ****************************************************************************/
  // Generate TPM EK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmEk, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_ek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                 tbs_certs.tpm_ek_tbs_certificate,
                                 &tbs_certs.tpm_ek_tbs_certificate_size));
  LOG_INFO("Generated TPM EK TBS certificate.");

  // Generate TPM CEK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmCek, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  tbs_certs.tpm_cek_tbs_certificate,
                                  &tbs_certs.tpm_cek_tbs_certificate_size));
  LOG_INFO("Generated TPM CEK TBS certificate.");

  // Generate TPM CIK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmCik, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cik_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  tbs_certs.tpm_cik_tbs_certificate,
                                  &tbs_certs.tpm_cik_tbs_certificate_size));
  LOG_INFO("Generated TPM CIK TBS certificate.");

  /*****************************************************************************
   * Certificate Export and Endorsement.
   ****************************************************************************/
  // Export the certificates to the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Exporting TBS certificates ...");
  RESP_OK(ujson_serialize_manuf_certs_t, uj, &tbs_certs);

  // Import endorsed certificates from the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Importing endorsed certificates ...");
  TRY(ujson_deserialize_manuf_endorsed_certs_t(uj, &endorsed_certs));

  /*****************************************************************************
   * Save Certificates to Flash.
   ****************************************************************************/
  // DICE UDS Certificate.
  TRY(flash_ctrl_info_write(
      &kFlashCtrlInfoPageUdsCertificate, /*offset=*/0,
      size_to_words(get_cert_size(endorsed_certs.uds_certificate)),
      endorsed_certs.uds_certificate));
  LOG_INFO("Imported DICE UDS certificate.");

  // TPM Certificates (all on the same flash INFO page).
  uint32_t page_offset = 0;
  for (size_t i = 0; i < ARRAYSIZE(kEndorsedTpmCerts); i++) {
    const char *names[] = {"EK", "CEK", "CIK"};
    // Number of words necessary for certificate storage.
    uint32_t cert_size_words =
        size_to_words(get_cert_size(kEndorsedTpmCerts[i]));
    uint32_t cert_size_bytes = cert_size_words * sizeof(uint32_t);

    if ((page_offset + cert_size_bytes) > FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
      LOG_ERROR("TPM %s Certificate did not fit into the info page.", names[i]);
      return OUT_OF_RANGE();
    }
    TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageTpmCerts, page_offset,
                              cert_size_words, kEndorsedTpmCerts[i]));
    LOG_INFO("Imported TPM %s certificate.", names[i]);
    page_offset += cert_size_bytes;

    // Each certificate must be 8 bytes aligned.
    page_offset = round_up_to(page_offset, 3);
  }

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Finished importing certificates.");

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();
  log_self_hash();
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  CHECK_STATUS_OK(personalize_otp_and_flash_secrets(&uj));
  CHECK_STATUS_OK(personalize_dice_certificates(&uj));
  CHECK_STATUS_OK(log_hash_of_all_certs(&uj));
  return true;
}
