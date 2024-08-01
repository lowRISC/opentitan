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
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cert.h"
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
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

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
    .sizes =
        {
            // DICE certs.
            kUdsMaxTbsSizeBytes,
            kCdi0MaxCertSizeBytes,
            kCdi1MaxCertSizeBytes,
            // TPM certs.
            kTpmEkMaxTbsSizeBytes,
            kTpmCekMaxTbsSizeBytes,
            kTpmCikMaxTbsSizeBytes,
        },
    .offsets = {0},
    .tbs = {true, false, false, true, true, true},
    .certs = {0},
};
static manuf_certs_t endorsed_certs;

/**
 * Certificates flash info page layout.
 */
enum {
  /**
   * Order of the endorsed certificates within the `tbs_certs` struct.
   *
   * While the name of the struct is `tbs_certs`, it contains two fully endorsed
   * certificates (namely the CDI_0 and CDI_1 DICE certificates) to minimize the
   * data transfers between the host and device, since these certs are endorsed
   * on the device at creation time.
   */
  kCdi0EndorsedCertIdx = 1,
  kCdi1EndorsedCertIdx = 2,
  /**
   * Order of the certificates within the `endorsed_certs` struct.
   */
  kUdsEndorsedCertIdx = 0,
  kTpmEkEndorsedCertIdx = 1,
  kTpmCekEndorsedCertIdx = 2,
  kTpmCikEndorsedCertIdx = 3,
};
static const char *kDiceCertNames[] = {"UDS", "CDI_0", "CDI_1"};
static const char *kTpmCertNames[] = {"EK", "CEK", "CIK"};
// DICE cert buffers and offsets.
static const unsigned char *kEndorsedDiceCerts[] = {
    endorsed_certs.certs,
    tbs_certs.certs,
    tbs_certs.certs,
};
static const uint32_t *kDiceCertOffsets[] = {
    endorsed_certs.offsets,
    tbs_certs.offsets,
    tbs_certs.offsets,
};
static const int kDiceCertOffsetIdxs[] = {
    kUdsEndorsedCertIdx,
    kCdi0EndorsedCertIdx,
    kCdi1EndorsedCertIdx,
};
// TPM cert buffers and offsets.
static const unsigned char *kEndorsedTpmCerts[] = {
    endorsed_certs.certs,
    endorsed_certs.certs,
    endorsed_certs.certs,
};
static const uint32_t *kTpmCertOffsets[] = {
    endorsed_certs.offsets,
    endorsed_certs.offsets,
    endorsed_certs.offsets,
};
static const int kTpmCertOffsetIdxs[] = {
    kTpmEkEndorsedCertIdx,
    kTpmCekEndorsedCertIdx,
    kTpmCikEndorsedCertIdx,
};
static const cert_flash_info_layout_t kCertFlashInfoLayout[] = {
    {
        .info_page = &kFlashCtrlInfoPageDiceCerts,
        .num_certs = 3,
        .group_name = "DICE",
        .names = kDiceCertNames,
        .certs = kEndorsedDiceCerts,
        .cert_offsets = kDiceCertOffsets,
        .cert_offset_idxs = kDiceCertOffsetIdxs,
    },
    {
        .info_page = &kFlashCtrlInfoPageTpmCerts,
        .num_certs = 3,
        .group_name = "TPM",
        .names = kTpmCertNames,
        .certs = kEndorsedTpmCerts,
        .cert_offsets = kTpmCertOffsets,
        .cert_offset_idxs = kTpmCertOffsetIdxs,
    },
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
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageTpmCerts);
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageDiceCerts,
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

  // Provision OTP Secret2 partition and flash info pages 1, 2, and 4 (keymgr
  // and DICE keygen seeds).
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    LOG_INFO("Waiting for host public key ...");
    TRY(ujson_deserialize_ecc_p256_public_key_t(uj, &host_ecc_pk));
    TRY(manuf_personalize_device_secrets(&flash_ctrl_state, &lc_ctrl, &otp_ctrl,
                                         &host_ecc_pk, &wrapped_rma_token));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldUdsAttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldCdi0AttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldCdi1AttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldTpmEkAttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldTpmCekAttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldTpmCikAttestationKeySeed,
        kAttestationSeedWords));
    // Provision the attestation key generation version field (at the end of the
    // attestation seed info page).
    uint32_t kKeyGenVersion = kAttestationKeyGenVersion0;
    TRY(manuf_flash_info_field_write(
        &flash_ctrl_state, kFlashInfoFieldAttestationKeyGenVersion,
        /*data_in=*/&kKeyGenVersion, /*num_words=*/1,
        /*erase_page_before_write=*/false));
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
  cert_size = cert_x509_asn1_decode_size_header(buffer);
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
  TRY(flash_ctrl_info_read(page, offset,
                           util_size_to_words(cert_size - bytes_read),
                           buffer + bytes_read));
  hmac_sha256_update(buffer, cert_size);

  if (size) {
    *size = cert_size;
  }
  return OK_STATUS();
}

static status_t log_hash_of_all_certs(ujson_t *uj) {
  uint32_t cert_size;
  serdes_sha256_hash_t hash;
  hmac_sha256_init();

  // Push all certificates into the hash.
  for (size_t i = 0; i < ARRAYSIZE(kCertFlashInfoLayout); i++) {
    uint32_t page_offset = 0;
    const cert_flash_info_layout_t curr_layout = kCertFlashInfoLayout[i];
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      TRY(hash_certificate(curr_layout.info_page, page_offset, &cert_size));
      page_offset += util_size_to_words(cert_size) * sizeof(uint32_t);
      page_offset = util_round_up_to(page_offset, 3);
    }
  }

  // Log the final hash of all certificates to the host and console.
  hmac_sha256_process();
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
  size_t curr_cert_offset = 0;
  size_t curr_cert_idx = 0;

  // Generate UDS keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyUds, &uds_pubkey_id, &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kOtbnBootAttestationKeyTypeDice,
                                     kUdsKeymgrDiversifier));
  TRY(dice_uds_tbs_cert_build(&uds_key_ids, &curr_pubkey,
                              &tbs_certs.certs[curr_cert_offset],
                              &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
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
      &tbs_certs.certs[curr_cert_offset], &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
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
      &tbs_certs.certs[curr_cert_offset], &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
  LOG_INFO("Generated CDI_1 certificate.");

  /*****************************************************************************
   * TPM certificates.
   ****************************************************************************/
  // Generate TPM EK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmEk, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_ek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                 &tbs_certs.certs[curr_cert_offset],
                                 &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
  LOG_INFO("Generated TPM EK TBS certificate.");

  // Generate TPM CEK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmCek, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  &tbs_certs.certs[curr_cert_offset],
                                  &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
  LOG_INFO("Generated TPM CEK TBS certificate.");

  // Generate TPM CIK keys and (TBS) cert.
  TRY(dice_attestation_keygen(kDiceKeyTpmCik, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cik_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  &tbs_certs.certs[curr_cert_offset],
                                  &tbs_certs.sizes[curr_cert_idx]));
  tbs_certs.offsets[curr_cert_idx] = curr_cert_offset;
  curr_cert_offset += tbs_certs.sizes[curr_cert_idx];
  curr_cert_idx++;
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
  TRY(ujson_deserialize_manuf_certs_t(uj, &endorsed_certs));

  /*****************************************************************************
   * Save Certificates to Flash.
   ****************************************************************************/
  for (size_t i = 0; i < ARRAYSIZE(kCertFlashInfoLayout); i++) {
    uint32_t page_offset = 0;
    const cert_flash_info_layout_t curr_layout = kCertFlashInfoLayout[i];
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      // Number of words necessary for certificate storage (rounded up to word
      // alignment).
      uint32_t cert_offset =
          curr_layout.cert_offsets[j][curr_layout.cert_offset_idxs[j]];
      uint32_t cert_size_words =
          util_size_to_words(cert_x509_asn1_decode_size_header(
              &curr_layout.certs[j][cert_offset]));
      uint32_t cert_size_bytes = cert_size_words * sizeof(uint32_t);

      if ((page_offset + cert_size_bytes) > FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
        LOG_ERROR("%s %s certificate did not fit into the info page.",
                  curr_layout.group_name, curr_layout.names[j]);
        return OUT_OF_RANGE();
      }
      TRY(flash_ctrl_info_write(curr_layout.info_page, page_offset,
                                cert_size_words,
                                &curr_layout.certs[j][cert_offset]));
      LOG_INFO("Imported %s %s certificate.", curr_layout.group_name,
               curr_layout.names[j]);
      page_offset += cert_size_bytes;

      // Each certificate must be 8 bytes aligned (flash word size).
      page_offset = util_round_up_to(page_offset, 3);
    }
  }

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Finished importing certificates.");

  return OK_STATUS();
}

/**
 * A custom extension to the personalization flow to enable various SKU owners
 * to customize the provisioning of their devices.
 */
extern status_t personalize_extension(ujson_t *uj);

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();
  log_self_hash();
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  CHECK_STATUS_OK(personalize_otp_and_flash_secrets(&uj));
  CHECK_STATUS_OK(personalize_dice_certificates(&uj));
  CHECK_STATUS_OK(log_hash_of_all_certs(&uj));
  CHECK_STATUS_OK(personalize_extension(&uj));

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Personalization done.");

  return true;
}
