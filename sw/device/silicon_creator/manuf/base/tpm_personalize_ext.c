// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/tpm.h"
#include "sw/device/silicon_creator/lib/cert/tpm_cek.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_cik.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"   // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Peripheral handles.
 */
static dif_flash_ctrl_state_t flash_ctrl_state;

/**
 * Certificate data.
 */
static hmac_digest_t tpm_endorsement_key_id;
static hmac_digest_t tpm_pubkey_id;
static cert_key_id_pair_t tpm_key_ids = {.endorsement = &tpm_endorsement_key_id,
                                         .cert = &tpm_pubkey_id};
static ecdsa_p256_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static char *kTpmCertNames[] = {"EK", "CEK", "CIK"};

/**
 * Initializes all DIF handles used in this program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  return OK_STATUS();
}

enum {
  /**
   * Indices of the TPM TBS certificates in the `tbs_certs` struct that is sent
   * to the host during personalization.
   */
  kTpmEkTbsCertStructIdx = 3,
  kTpmCekTbsCertStructIdx = 4,
  kTpmCikTbsCertStructIdx = 5,

  /**
   * Index of the `cert_flash_layout` array in the `ft_personalize.c` base
   * firmware to use to hold the additional TPM certificates.
   */
  kTpmCertFlashLayoutIdx = 1,
};

/**
 * Configures flash info pages to store device certificates.
 */
static status_t config_and_erase_tpm_certificate_flash_pages(void) {
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageOwnerReserved7);
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerReserved7,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

static status_t personalize_gen_tpm_certificates(
    ujson_t *uj, manuf_certgen_inputs_t *certgen_inputs,
    manuf_certs_t *tbs_certs, cert_flash_info_layout_t *cert_flash_layout) {
  size_t curr_cert_size = 0;

  // Set the endorsement key ID.
  memcpy(tpm_endorsement_key_id.digest, certgen_inputs->auth_key_key_id,
         kCertKeyIdSizeInBytes);

  // Add three certs to the total number of certs set to the host.
  tbs_certs->num_certs += 3;

  // All three TPM certificates will need host-side endorsing.
  tbs_certs->tbs[kTpmEkTbsCertStructIdx] = true;
  tbs_certs->tbs[kTpmCekTbsCertStructIdx] = true;
  tbs_certs->tbs[kTpmCikTbsCertStructIdx] = true;

  // Set the flash info page layout.
  cert_flash_layout[kTpmCertFlashLayoutIdx].used = true;
  cert_flash_layout[kTpmCertFlashLayoutIdx].group_name = "TPM";
  cert_flash_layout[kTpmCertFlashLayoutIdx].num_certs = 3;
  cert_flash_layout[kTpmCertFlashLayoutIdx].names = kTpmCertNames;

  // Provision TPM keygen seeds to flash info.
  TRY(manuf_personalize_flash_asymm_key_seed(
      &flash_ctrl_state, kFlashInfoFieldTpmEkAttestationKeySeed,
      kAttestationSeedWords));
  TRY(manuf_personalize_flash_asymm_key_seed(
      &flash_ctrl_state, kFlashInfoFieldTpmCekAttestationKeySeed,
      kAttestationSeedWords));
  TRY(manuf_personalize_flash_asymm_key_seed(
      &flash_ctrl_state, kFlashInfoFieldTpmCikAttestationKeySeed,
      kAttestationSeedWords));

  // Generate TPM EK keys and (TBS) cert.
  curr_cert_size = kTpmEkMaxTbsSizeBytes;
  TRY(cert_ecc_p256_keygen(kTpmKeyEk, &tpm_pubkey_id, &curr_pubkey));
  TRY(tpm_ek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                            &tbs_certs->certs[tbs_certs->next_free],
                            &curr_cert_size));
  tbs_certs->next_free += curr_cert_size;
  LOG_INFO("Generated TPM EK TBS certificate.");

  // Generate TPM CEK keys and (TBS) cert.
  curr_cert_size = kTpmCekMaxTbsSizeBytes;
  TRY(cert_ecc_p256_keygen(kTpmKeyCek, &tpm_pubkey_id, &curr_pubkey));
  TRY(tpm_cek_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                             &tbs_certs->certs[tbs_certs->next_free],
                             &curr_cert_size));
  tbs_certs->next_free += curr_cert_size;
  LOG_INFO("Generated TPM CEK TBS certificate.");

  // Generate TPM CIK keys and (TBS) cert.
  curr_cert_size = kTpmCikMaxTbsSizeBytes;
  TRY(cert_ecc_p256_keygen(kTpmKeyCik, &tpm_pubkey_id, &curr_pubkey));
  TRY(tpm_cik_tbs_cert_build(&tpm_key_ids, &curr_pubkey,
                             &tbs_certs->certs[tbs_certs->next_free],
                             &curr_cert_size));
  tbs_certs->next_free += curr_cert_size;
  LOG_INFO("Generated TPM CIK TBS certificate.");

  return OK_STATUS();
}

status_t personalize_extension_pre_cert_endorse(
    ujson_t *uj, manuf_certgen_inputs_t *certgen_inputs,
    manuf_certs_t *tbs_certs, cert_flash_info_layout_t *cert_flash_layout) {
  LOG_INFO("Running TPM perso extension ...");
  TRY(peripheral_handles_init());
  TRY(config_and_erase_tpm_certificate_flash_pages());
  TRY(personalize_gen_tpm_certificates(uj, certgen_inputs, tbs_certs,
                                       cert_flash_layout));
  return OK_STATUS();
}

status_t personalize_extension_post_cert_endorse(
    ujson_t *uj, manuf_certs_t *endorsed_certs,
    cert_flash_info_layout_t *cert_flash_layout) {
  /* Empty because it is unused but we still need to link to something. */
  return OK_STATUS();
}
