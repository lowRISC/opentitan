// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
#include "sw/device/silicon_creator/lib/dice.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/skus/earlgrey_a0/sival_bringup/util.h"

#include "flash_ctrl_regs.h"  // Generated.

// Check TBS certificate buffer sizes.
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_tpm_tbs_certs_t, tpm_ek_tbs_certificate,
                              OT_ALIGN_MEM(kTpmEkMaxTbsSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_tpm_tbs_certs_t, tpm_cek_tbs_certificate,
                              OT_ALIGN_MEM(kTpmCekMaxTbsSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_tpm_tbs_certs_t, tpm_cik_tbs_certificate,
                              OT_ALIGN_MEM(kTpmCikMaxTbsSizeBytes));

// Check endorsed certificate buffer sizes.
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_tpm_certs_t, tpm_ek_certificate,
                              OT_ALIGN_MEM(kTpmEkMaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_tpm_certs_t, tpm_cek_certificate,
                              OT_ALIGN_MEM(kTpmCekMaxCertSizeBytes));
OT_ASSERT_MEMBER_SIZE_AS_ENUM(manuf_endorsed_tpm_certs_t, tpm_cik_certificate,
                              OT_ALIGN_MEM(kTpmCikMaxCertSizeBytes));

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

/**
 * Certificate data.
 */
static manuf_certgen_inputs_t certgen_inputs;
static hmac_digest_t tpm_endorsement_key_id;
static hmac_digest_t tpm_pubkey_id;
static dice_cert_key_id_pair_t tpm_key_ids = {
    .endorsement = &tpm_endorsement_key_id, .cert = &tpm_pubkey_id};
static attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static manuf_tpm_tbs_certs_t tpm_certs = {
    .tpm_ek_tbs_certificate = {0},
    .tpm_ek_tbs_certificate_size = kTpmEkMaxTbsSizeBytes,
    .tpm_cek_tbs_certificate = {0},
    .tpm_cek_tbs_certificate_size = kTpmCekMaxTbsSizeBytes,
    .tpm_cik_tbs_certificate = {0},
    .tpm_cik_tbs_certificate_size = kTpmCikMaxTbsSizeBytes,
};
static manuf_endorsed_tpm_certs_t endorsed_tpm_certs;
static const unsigned char *kEndorsedTpmCerts[] = {
    endorsed_tpm_certs.tpm_ek_certificate,
    endorsed_tpm_certs.tpm_cek_certificate,
    endorsed_tpm_certs.tpm_cik_certificate,
};

/**
 * Keymgr binding values.
 */
static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};

/**
 * Configures TPM certificate flash info page.
 */
static status_t config_and_erase_certificate_flash_pages(void) {
  flash_ctrl_cert_info_pages_creator_cfg();
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageTpmCerts,
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
  for (size_t i = 0; i < ARRAYSIZE(kEndorsedTpmCerts);
       i++) {  // There are three TPM certificates on the page.
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
 * Crank the keymgr to produce the TPM attestation keys and certificates.
 */
static status_t personalize(ujson_t *uj) {
  // Load OTBN attestation keygen program.
  TRY(otbn_boot_app_load());

  // Retrieve certificate provisioning data.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Waiting for TPM certificate inputs ...");
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, &certgen_inputs));
  // We copy over the UDS endorsement key ID to an SHA256 digest type, since
  // this is the format of key IDs generated on-dice.
  memcpy(tpm_endorsement_key_id.digest, certgen_inputs.auth_key_key_id,
         kDiceCertKeyIdSizeInBytes);

  // Configure certificate flash info page permissions.
  TRY(config_and_erase_certificate_flash_pages());

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to OwnerKey state.
  TRY(keymgr_state_check(kKeymgrStateReset));
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateInit));
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateCreatorRootKey));
  compute_keymgr_owner_int_binding(&certgen_inputs);
  TRY(keymgr_owner_int_advance(&sealing_binding_value,
                               &attestation_binding_value,
                               /*max_key_version=*/0));
  TRY(keymgr_state_check(kKeymgrStateOwnerIntermediateKey));
  compute_keymgr_owner_binding(&certgen_inputs);
  TRY(keymgr_owner_advance(&sealing_binding_value, &attestation_binding_value,
                           /*max_key_version=*/0));

  // Generate TPM EK keys and TBS.
  TRY(dice_attestation_keygen(kDiceKeyTpmEk, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_ek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                 tpm_certs.tpm_ek_tbs_certificate,
                                 &tpm_certs.tpm_ek_tbs_certificate_size));
  LOG_INFO("Generated TPM EK TBS certificate.");

  // Generate TPM CEK keys and TBS.
  TRY(dice_attestation_keygen(kDiceKeyTpmCek, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  tpm_certs.tpm_cek_tbs_certificate,
                                  &tpm_certs.tpm_cek_tbs_certificate_size));
  LOG_INFO("Generated TPM CEK TBS certificate.");

  // Generate TPM CIK keys and TBS.
  TRY(dice_attestation_keygen(kDiceKeyTpmCik, &tpm_pubkey_id, &curr_pubkey));
  TRY(dice_tpm_cik_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                                  tpm_certs.tpm_cik_tbs_certificate,
                                  &tpm_certs.tpm_cik_tbs_certificate_size));
  LOG_INFO("Generated TPM CIK TBS certificate.");

  // Export the certificates to the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Exporting TPM certificates ...");
  RESP_OK(ujson_serialize_manuf_tpm_tbs_certs_t, uj, &tpm_certs);

  // Import endorsed certificates from the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Importing endorsed TPM certificates ...");
  TRY(ujson_deserialize_manuf_endorsed_tpm_certs_t(uj, &endorsed_tpm_certs));

  // Write the endorsed certificates to flash and ack to host.
  uint32_t page_offset = 0;
  for (size_t i = 0; i < ARRAYSIZE(kEndorsedTpmCerts); i++) {
    const char *names[] = {"EK", "CEK", "CIK"};
    // Number of words necessary for certificate storage.
    uint32_t cert_size_words =
        size_to_words(get_cert_size(kEndorsedTpmCerts[i]));
    uint32_t cert_size_bytes = cert_size_words * sizeof(uint32_t);

    if ((page_offset + cert_size_bytes) > FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
      LOG_ERROR("TPM %s certificate did not fit into the info page.", names[i]);
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
  ujson_t uj = ujson_ottf_console();

  log_self_hash();
  CHECK_STATUS_OK(personalize(&uj));
  CHECK_STATUS_OK(log_hash_of_all_certs(&uj));

  return true;
}
