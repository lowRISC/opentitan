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
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/base/personalize_ext.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

enum {
  /**
   * Size of the largest OTP partition to be measured.
   */
  kDiceMeasuredOtpPartitionMaxSizeIn32bitWords =
      (OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
       OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
      sizeof(uint32_t),
};

static uint32_t otp_state[kDiceMeasuredOtpPartitionMaxSizeIn32bitWords] = {0};

// clang-format off
static_assert(
    OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE > OTP_CTRL_PARAM_CREATOR_SW_CFG_SIZE &&
    OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE > OTP_CTRL_PARAM_ROT_CREATOR_AUTH_CODESIGN_SIZE &&
    OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE > OTP_CTRL_PARAM_ROT_CREATOR_AUTH_STATE_SIZE,
    "The largest DICE measured OTP partition is no longer the "
    "OwnerSwCfg partition. Update the "
    "kDiceMeasuredOtpPartitionMaxSizeIn32bitWords constant.");
// clang-format on

/**
 * Peripheral handles.
 */
static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_rstmgr_t rstmgr;

/**
 * Keymgr binding values.
 */
static keymgr_binding_value_t attestation_binding_value = {.data = {0}};
static keymgr_binding_value_t sealing_binding_value = {.data = {0}};

/**
 * Certificate data.
 */
static hmac_digest_t otp_creator_sw_cfg_measurement;
static hmac_digest_t otp_owner_sw_cfg_measurement;
static hmac_digest_t otp_rot_creator_auth_codesign_measurement;
static hmac_digest_t otp_rot_creator_auth_state_measurement;
static manuf_certgen_inputs_t certgen_inputs;
static hmac_digest_t uds_endorsement_key_id;
static hmac_digest_t uds_pubkey_id;
static hmac_digest_t cdi_0_pubkey_id;
static hmac_digest_t cdi_1_pubkey_id;
static cert_key_id_pair_t uds_key_ids = {
    .endorsement = &uds_endorsement_key_id,
    .cert = &uds_pubkey_id,
};
static cert_key_id_pair_t cdi_0_key_ids = {
    .endorsement = &uds_pubkey_id,
    .cert = &cdi_0_pubkey_id,
};
static cert_key_id_pair_t cdi_1_key_ids = {
    .endorsement = &cdi_0_pubkey_id,
    .cert = &cdi_1_pubkey_id,
};
static ecdsa_p256_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
static perso_blob_t perso_blob_to_host;    // Perso data device => host.
static perso_blob_t perso_blob_from_host;  // Perso data host => device.

/**
 * Certificates flash info page layout.
 */
static uint8_t all_certs[8192];
static size_t cdi_0_offset;
static size_t cdi_1_offset;
static cert_flash_info_layout_t cert_flash_layout[] = {
    {
        .used = true,
        .group_name = "DICE",
        .info_page = &kFlashCtrlInfoPageDiceCerts,
        .num_certs = 3,
    },
    // These flash info pages can be used by provisioning extensions to store
    // additional certificates SKU owners may desire to provision.
    {
        .used = false,
        .group_name = "Ext0",
        .info_page = &kFlashCtrlInfoPageOwnerReserved7,
        .num_certs = 0,
    },
    {
        .used = false,
        .group_name = "Ext1",
        .info_page = &kFlashCtrlInfoPageOwnerReserved8,
        .num_certs = 0,
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
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageDiceCerts,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

/**
 * Helper function to compute measurements of various OTP partitions that are to
 * be included in attestation certificates.
 */
static status_t measure_otp_partition(otp_partition_t partition,
                                      hmac_digest_t *measurement) {
  // Compute the digest.
  otp_dai_read(partition, /*address=*/0, otp_state,
               kOtpPartitions[partition].size / sizeof(uint32_t));

  hmac_sha256(otp_state, kOtpPartitions[partition].size, measurement);

  // Check the digest matches what is stored in OTP.
  // TODO(#21554): remove this conditional once the root keys and key policies
  // have been provisioned. Until then, these partitions have not been locked.
  if (partition == kOtpPartitionCreatorSwCfg ||
      partition == kOtpPartitionOwnerSwCfg) {
    uint64_t expected_digest = otp_partition_digest_read(partition);
    uint32_t digest_hi = expected_digest >> 32;
    uint32_t digest_lo = expected_digest & UINT32_MAX;
    HARDENED_CHECK_EQ(digest_hi, measurement->digest[1]);
    HARDENED_CHECK_EQ(digest_lo, measurement->digest[0]);
  }
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

  // The last bootstrap process in the perso flow is done.
  // Complete the provisioning of OTP OwnerSwCfg partition.
  if (!status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_rom_bootstrap_dis_cfg(&otp_ctrl));
    TRY(manuf_individualize_device_owner_sw_cfg_lock(&otp_ctrl));
  }

  // Provision OTP Secret2 partition and flash info pages 1, 2, and 4 (keymgr
  // and DICE keygen seeds).
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    lc_token_hash_t token_hash;
    // Wait for host the host generated RMA unlock token hash to arrive over the
    // console.
    LOG_INFO("Waiting For RMA Unlock Token Hash ...");
    CHECK_STATUS_OK(
        UJSON_WITH_CRC(ujson_deserialize_lc_token_hash_t, uj, &token_hash));

    TRY(manuf_personalize_device_secrets(&flash_ctrl_state, &lc_ctrl, &otp_ctrl,
                                         &token_hash));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldUdsAttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldCdi0AttestationKeySeed,
        kAttestationSeedWords));
    TRY(manuf_personalize_flash_asymm_key_seed(
        &flash_ctrl_state, kFlashInfoFieldCdi1AttestationKeySeed,
        kAttestationSeedWords));
    // Provision the attestation key generation version field (at the end of the
    // attestation seed info page).
    uint32_t kKeyGenVersion = kAttestationKeyGenVersion0;
    TRY(manuf_flash_info_field_write(
        &flash_ctrl_state, kFlashInfoFieldAttestationKeyGenVersion,
        /*data_in=*/&kKeyGenVersion, /*num_words=*/1,
        /*erase_page_before_write=*/false));
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

static status_t hash_all_certs(void) {
  uint32_t cert_size;
  hmac_sha256_init();

  // Push all certificates into the hash.
  for (size_t i = 0; i < ARRAYSIZE(cert_flash_layout); i++) {
    uint32_t page_offset = 0;
    const cert_flash_info_layout_t curr_layout = cert_flash_layout[i];
    // Skip the page if it is not in use.
    if (!curr_layout.used) {
      continue;
    }
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      TRY(hash_certificate(curr_layout.info_page, page_offset, &cert_size));
      page_offset += util_size_to_words(cert_size) * sizeof(uint32_t);
      page_offset = util_round_up_to(page_offset, 3);
    }
  }

  return OK_STATUS();
}

/**
 * Crank the keymgr to produce the DICE attestation keys and certificates.
 */
static status_t personalize_gen_dice_certificates(ujson_t *uj) {
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
         kCertKeyIdSizeInBytes);

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init());
  TRY(kmac_keymgr_configure());

  // Advance keymgr to CreatorRootKey state.
  TRY(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  TRY(sc_keymgr_state_check(kScKeymgrStateInit));
  sc_keymgr_advance_state();

  // Measure OTP partitions.
  //
  // Note: we do not measure HwCfg0 as this is the Device ID, which is already
  // mixed into the keyladder directly via hardware channels.
  TRY(measure_otp_partition(kOtpPartitionCreatorSwCfg,
                            &otp_creator_sw_cfg_measurement));
  TRY(measure_otp_partition(kOtpPartitionOwnerSwCfg,
                            &otp_owner_sw_cfg_measurement));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthCodesign,
                            &otp_rot_creator_auth_codesign_measurement));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthState,
                            &otp_rot_creator_auth_state_measurement));

  /*****************************************************************************
   * DICE certificates.
   ****************************************************************************/
  size_t curr_cert_size = 0;

  // Generate UDS keys and (TBS) cert.
  curr_cert_size = kUdsMaxTbsSizeBytes;
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyUds, &uds_pubkey_id,
                                     &curr_pubkey));
  TRY(otbn_boot_attestation_key_save(kDiceKeyUds.keygen_seed_idx,
                                     kDiceKeyUds.type,
                                     *kDiceKeyUds.keymgr_diversifier));

  // Build the certificate in a temp buffer, use all_certs for that.
  TRY(dice_uds_tbs_cert_build(
      &otp_creator_sw_cfg_measurement, &otp_owner_sw_cfg_measurement,
      &otp_rot_creator_auth_codesign_measurement,
      &otp_rot_creator_auth_state_measurement, &uds_key_ids, &curr_pubkey,
      all_certs, &curr_cert_size));
  TRY(perso_tlv_prepare_cert_for_shipping("UDS", true, all_certs,
                                          curr_cert_size, &perso_blob_to_host));

  // Generate CDI_0 keys and cert.
  curr_cert_size = kCdi0MaxCertSizeBytes;
  compute_keymgr_owner_int_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_int_advance(&sealing_binding_value,
                                  &attestation_binding_value,
                                  /*max_key_version=*/0));
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyCdi0, &cdi_0_pubkey_id,
                                     &curr_pubkey));
  TRY(dice_cdi_0_cert_build((hmac_digest_t *)certgen_inputs.rom_ext_measurement,
                            certgen_inputs.rom_ext_security_version,
                            &cdi_0_key_ids, &curr_pubkey, all_certs,
                            &curr_cert_size));
  cdi_0_offset = perso_blob_to_host.next_free;
  TRY(perso_tlv_prepare_cert_for_shipping("CDI_O", false, all_certs,
                                          curr_cert_size, &perso_blob_to_host));

  // Generate CDI_1 keys and cert.
  curr_cert_size = kCdi1MaxCertSizeBytes;
  compute_keymgr_owner_binding(&certgen_inputs);
  TRY(sc_keymgr_owner_advance(&sealing_binding_value,
                              &attestation_binding_value,
                              /*max_key_version=*/0));
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyCdi1, &cdi_1_pubkey_id,
                                     &curr_pubkey));
  TRY(dice_cdi_1_cert_build(
      (hmac_digest_t *)certgen_inputs.owner_measurement,
      (hmac_digest_t *)certgen_inputs.owner_manifest_measurement,
      certgen_inputs.owner_security_version, &cdi_1_key_ids, &curr_pubkey,
      all_certs, &curr_cert_size));
  cdi_1_offset = perso_blob_to_host.next_free;
  return perso_tlv_prepare_cert_for_shipping(
      "CDI_1", false, all_certs, curr_cert_size, &perso_blob_to_host);
}

// How much data could there be in the receive buffer.
static size_t max_available(void) {
  if (perso_blob_from_host.next_free > sizeof(perso_blob_from_host.body))
    return 0;  // This could never happen, but just in case.

  return sizeof(perso_blob_from_host.body) - perso_blob_from_host.next_free;
}

/**
 * Find the next certificate object in the receive perso buffer and copy it out
 * to the passed in location.
 *
 * @param dest pointer to pointer in the destination buffer, this function
 *             advances the pointer by the size of the copied certificate
 * @param free_room pointer to the size of the destination buffer, this function
 *             reduces the size of the buffer by the size of the copied
 *             certificate
 */
static status_t extract_next_cert(uint8_t **dest, size_t *free_room) {
  // A just in case sanity check.
  if (perso_blob_from_host.next_free > sizeof(perso_blob_from_host.body)) {
    return INTERNAL();  // Something is really screwed up.
  }

  // Scan the received buffer until the next endorsed cert is found.
  while (perso_blob_from_host.num_objs != 0) {
    perso_tlv_cert_block_t block;
    status_t status;

    status = perso_tlv_set_cert_block(
        perso_blob_from_host.body + perso_blob_from_host.next_free,
        max_available(), &block);
    switch (status_err(status)) {
      case kOk:
        break;
      case kNotFound: {
        // The object must be not an endorsed certificate.
        perso_blob_from_host.next_free += block.obj_size;
        perso_blob_from_host.num_objs--;
        continue;
      }
      default:
        return status;
    }
    if (*free_room < block.wrapped_cert_size)
      return RESOURCE_EXHAUSTED();  // Another case of really screwed up.

    uint8_t *dest_p = *dest;
    memcpy(dest_p, block.wrapped_cert_p, block.wrapped_cert_size);
    LOG_INFO("Copied %s certificate", block.name);

    *dest = dest_p + block.wrapped_cert_size;
    *free_room = *free_room - block.wrapped_cert_size;

    perso_blob_from_host.next_free +=
        block.wrapped_cert_size + sizeof(perso_tlv_object_header_t);
    perso_blob_from_host.num_objs--;
    return OK_STATUS();
  }
  return OK_STATUS();
}

static status_t personalize_endorse_certificates(ujson_t *uj) {
  /*****************************************************************************
   * Certificate Export and Endorsement.
   ****************************************************************************/
  // Export the certificates to the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Exporting TBS certificates ...");

  RESP_OK(ujson_serialize_perso_blob_t, uj, &perso_blob_to_host);

  // Import endorsed certificates from the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Importing endorsed certificates ...");
  TRY(ujson_deserialize_perso_blob_t(uj, &perso_blob_from_host));

  /*****************************************************************************
   * Rearrange certificates to prepare for writing to flash.
   *
   * All certificates are ordered in a buffer according to the order in which
   * they will be written to flash. That order is:
   * 1. UDS cert
   * 2. CDI_0 cert
   * 3. CDI_1 cert
   * 4. Provision Extension certs
   ****************************************************************************/
  // We start scanning the received buffer from zero, the assumption is that the
  // endorsed UDS cert is the first certificate in the buffer (even if preceeded
  // by other types of objects).
  perso_blob_from_host.next_free = 0;
  // Location where the next cert will be copied.
  uint8_t *next_cert = all_certs;
  // How much room left in the destination buffer.
  size_t free_room = sizeof(all_certs);
  // Helper structure caching certificate information.
  perso_tlv_cert_block_t block;
  // UDS cert.
  TRY(extract_next_cert(&next_cert, &free_room));

  // Now the two CDI certs which were endorsed locally and sent to the host
  // earlier.
  size_t cdis[] = {cdi_0_offset, cdi_1_offset};
  for (size_t i = 0; i < ARRAYSIZE(cdis); i++) {
    size_t offset = cdis[i];
    TRY(perso_tlv_set_cert_block(perso_blob_to_host.body + offset,
                                 sizeof(perso_blob_to_host.body) - offset,
                                 &block));
    if (block.wrapped_cert_size > free_room)
      return RESOURCE_EXHAUSTED();

    memcpy(next_cert, block.wrapped_cert_p, block.wrapped_cert_size);
    LOG_INFO("Copied %s certificate", block.name);
    next_cert += block.wrapped_cert_size;
    free_room -= block.wrapped_cert_size;
  }

  // Now the rest of endorsed certificates received from the host, if any.
  while (perso_blob_from_host.num_objs)
    TRY(extract_next_cert(&next_cert, &free_room));

  /*****************************************************************************
   * Save Certificates to Flash.
   ****************************************************************************/
  // This is where the certificates to be copied are stored, each one wrapped in
  // with its name prepended to it.
  uint8_t *certs = all_certs;
  for (size_t i = 0; i < ARRAYSIZE(cert_flash_layout); i++) {
    const cert_flash_info_layout_t curr_layout = cert_flash_layout[i];
    uint32_t page_offset = 0;

    // Skip the page if it is not in use.
    if (!curr_layout.used) {
      continue;
    }

    // This is a bit brittle, but we expect the sum of {layout}.num_certs values
    // in the following flash layout sections to be equal to the number of
    // endorsed  extension certificates received from the host.
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      uint16_t name_len;
      char name[kCrthNameSizeFieldMask + 1];
      perso_tlv_cert_header_t crth;

      // We just prepared the set of wrapped certificates, let's trust that the
      // data is correct and does not need more validation.
      memcpy(&crth, certs, sizeof(crth));
      certs += sizeof(crth);
      PERSO_TLV_GET_FIELD(Crth, NameSize, crth, &name_len);
      memcpy(name, certs, name_len);
      name[name_len] = '\0';
      certs += name_len;

      // Compute the number of words necessary for certificate storage
      // (rounded up to word alignment).
      uint32_t cert_size_bytes = cert_x509_asn1_decode_size_header(certs);
      uint32_t cert_size_words = util_size_to_words(cert_size_bytes);
      uint32_t cert_size_bytes_ru = cert_size_words * sizeof(uint32_t);

      if ((page_offset + cert_size_bytes_ru) >
          FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
        LOG_ERROR("%s %s certificate did not fit into the info page.",
                  curr_layout.group_name, name);
        return OUT_OF_RANGE();
      }
      TRY(flash_ctrl_info_write(curr_layout.info_page, page_offset,
                                cert_size_words, certs));
      LOG_INFO("Imported %s %s certificate.", curr_layout.group_name, name);
      page_offset += cert_size_bytes_ru;
      certs += cert_size_bytes;

      // Each certificate must be 8 bytes aligned (flash word size).
      page_offset = util_round_up_to(page_offset, 3);
    }
  }

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Finished importing certificates.");

  return OK_STATUS();
}

static status_t send_final_hash(ujson_t *uj, serdes_sha256_hash_t *hash) {
  return RESP_OK(ujson_serialize_serdes_sha256_hash_t, uj, hash);
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  ujson_t uj = ujson_ottf_console();
  log_self_hash();
  CHECK_STATUS_OK(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  CHECK_STATUS_OK(personalize_otp_and_flash_secrets(&uj));
  CHECK_STATUS_OK(personalize_gen_dice_certificates(&uj));

  personalize_extension_pre_endorse_t pre_endorse = {
      .uj = &uj,
      .certgen_inputs = &certgen_inputs,
      .perso_blob_to_host = &perso_blob_to_host,
      .cert_flash_layout = cert_flash_layout,
      .flash_ctrl_handle = &flash_ctrl_state};
  CHECK_STATUS_OK(personalize_extension_pre_cert_endorse(&pre_endorse));

  CHECK_STATUS_OK(personalize_endorse_certificates(&uj));
  CHECK_STATUS_OK(hash_all_certs());

  personalize_extension_post_endorse_t post_endorse = {
      .uj = &uj,
      .perso_blob_from_host = &perso_blob_from_host,
      .cert_flash_layout = cert_flash_layout};
  CHECK_STATUS_OK(personalize_extension_post_cert_endorse(&post_endorse));

  // Log the hash of all perso objects to the host and console.
  serdes_sha256_hash_t hash;
  hmac_sha256_process();
  hmac_sha256_final((hmac_digest_t *)&hash);
  CHECK_STATUS_OK(send_final_hash(&uj, &hash));
  LOG_INFO("SHA256 hash of all perso objects: %08x%08x%08x%08x%08x%08x%08x%08x",
           hash.data[7], hash.data[6], hash.data[5], hash.data[4], hash.data[3],
           hash.data[2], hash.data[1], hash.data[0]);

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Personalization done.");

  return true;
}
