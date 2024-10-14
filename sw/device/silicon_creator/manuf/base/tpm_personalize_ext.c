// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "perso_tlv_data.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/tpm.h"
#include "sw/device/silicon_creator/lib/cert/tpm_ek.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/base/personalize_ext.h"
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
   * Index of the `cert_flash_layout` array in the `ft_personalize.c` base
   * firmware to use to hold the TPM EK certificate.
   */
  kTpmCertFlashLayoutIdx = 1,
};

/**
 * Configures flash info pages to store device certificates.
 */
static status_t config_and_erase_tpm_certificate_flash_pages(void) {
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageOwnerReserved6);
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageOwnerReserved6,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

// Temp buffer for storing generated EK certificate.
static uint8_t cert_buffer[kTpmEkMaxTbsSizeBytes];

static status_t personalize_gen_tpm_ek_certificate(
    manuf_certgen_inputs_t *certgen_inputs, perso_blob_t *perso_blob,
    cert_flash_info_layout_t *cert_flash_layout) {
  size_t curr_cert_size = 0;
  // Set the endorsement key ID.
  memcpy(tpm_endorsement_key_id.digest, certgen_inputs->auth_key_key_id,
         kCertKeyIdSizeInBytes);

  // Set the flash info page layout.
  cert_flash_layout[kTpmCertFlashLayoutIdx].used = true;
  cert_flash_layout[kTpmCertFlashLayoutIdx].group_name = "TPM";
  cert_flash_layout[kTpmCertFlashLayoutIdx].num_certs = 1;

  // Provision TPM keygen seeds to flash info.
  TRY(manuf_personalize_flash_asymm_key_seed(
      &flash_ctrl_state, kFlashInfoFieldTpmEkAttestationKeySeed,
      kAttestationSeedWords));

  // Generate TPM EK keys and (TBS) cert.
  TRY(otbn_boot_cert_ecc_p256_keygen(kTpmKeyEk, &tpm_pubkey_id, &curr_pubkey));

  curr_cert_size = sizeof(cert_buffer);
  TRY(tpm_ek_tbs_cert_build(&tpm_key_ids, &curr_pubkey, cert_buffer,
                            &curr_cert_size));
  return perso_tlv_prepare_cert_for_shipping("TPM EK", true, cert_buffer,
                                             curr_cert_size, perso_blob);
}

status_t personalize_extension_pre_cert_endorse(
    personalize_extension_pre_endorse_t *pre_params) {
  LOG_INFO("Running TPM perso extension ...");
  TRY(peripheral_handles_init());
  TRY(config_and_erase_tpm_certificate_flash_pages());
  TRY(personalize_gen_tpm_ek_certificate(pre_params->certgen_inputs,
                                         pre_params->perso_blob_to_host,
                                         pre_params->cert_flash_layout));
  return OK_STATUS();
}

status_t personalize_extension_post_cert_endorse(
    personalize_extension_post_endorse_t *post_params) {
  /* Empty because it is unused but we still need to link to something. */
  return OK_STATUS();
}
