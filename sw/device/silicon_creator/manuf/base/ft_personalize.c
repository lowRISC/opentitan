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
#include "sw/device/silicon_creator/lib/base/chip.h"
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
#include "sw/device/silicon_creator/lib/manifest.h"
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
static ecdsa_p256_public_key_t uds_pubkey = {.x = {0}, .y = {0}};
static perso_blob_t perso_blob_to_host;    // Perso data device => host.
static perso_blob_t perso_blob_from_host;  // Perso data host => device.

/**
 * Certificates flash info page layout.
 */
static uint8_t all_certs[8192];
static size_t uds_offset;
static size_t cdi_0_offset;
static size_t cdi_1_offset;
static cert_flash_info_layout_t cert_flash_layout[] = {
    {
        // The DICE UDS cert is placed on this page since it must remain stable
        // post manufacturing. This page should never be erased by ROM_EXT, nor
        // owner firmware.
        .used = true,
        .group_name = "FACTORY",
        .info_page = &kFlashCtrlInfoPageFactoryCerts,
        .num_certs = 1,
    },
    {
        .used = true,
        .group_name = "DICE",
        .info_page = &kFlashCtrlInfoPageDiceCerts,
        .num_certs = 2,
    },
    // These flash info pages can be used by provisioning extensions to store
    // additional certificates SKU owners may desire to provision.
    {
        .used = false,
        .group_name = "Ext0",
        .info_page = &kFlashCtrlInfoPageOwnerReserved6,
        .num_certs = 0,
    },
    {
        .used = false,
        .group_name = "Ext1",
        .info_page = &kFlashCtrlInfoPageOwnerReserved7,
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

/*
 * Return a pointer to the ROM_EXT manifest located in the slot b.
 */
static const manifest_t *rom_ext_manifest_b_get(void) {
  return (const manifest_t *)(TOP_EARLGREY_EFLASH_BASE_ADDR +
                              (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2));
}

extern const uint32_t kCreatorSwCfgManufStateValue;

/*
 * Check if the `identifier` field in slot_b is a ROM_EXT.
 */
static status_t check_next_slot_bootable(void) {
  TRY_CHECK(rom_ext_manifest_b_get()->identifier == CHIP_ROM_EXT_IDENTIFIER);
  return OK_STATUS();
}

/**
 * Initializes all DIF handles used in this program.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));
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
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageFactoryCerts);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  // No need to erase the kFlashCtrlInfoPageAttestationKeySeeds page as it is
  // erased on the first call to `manuf_personalize_flash_asymm_key_seed()`.
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageFactoryCerts,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageDiceCerts,
                            kFlashCtrlEraseTypePage));
  return OK_STATUS();
}

/**
 * Helper function to compute measurements of various OTP partitions that are to
 * be included in attestation certificates.
 */
static status_t measure_otp_partition(otp_partition_t partition,
                                      hmac_digest_t *measurement,
                                      bool use_expected_values) {
  // Compute the digest.
  otp_dai_read(partition, /*address=*/0, otp_state,
               kOtpPartitions[partition].size / sizeof(uint32_t));

  if (use_expected_values) {
    // Sets the expected values for fields in the OTP that are not provisioned
    // until the final stages of personalization.
    if (partition == kOtpPartitionOwnerSwCfg) {
      manuf_individualize_device_partition_expected_read(
          kDifOtpCtrlPartitionOwnerSwCfg, (uint8_t *)otp_state);
    } else if (partition == kOtpPartitionCreatorSwCfg) {
      manuf_individualize_device_partition_expected_read(
          kDifOtpCtrlPartitionCreatorSwCfg, (uint8_t *)otp_state);
    }
  }

  hmac_sha256(otp_state, kOtpPartitions[partition].size, measurement);

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
  if (!status_ok(
          manuf_individualize_device_flash_data_default_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl,
        OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET));
    LOG_INFO("Bootstrap requested.");
    wait_for_interrupt();
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
  hmac_sha256_process();
  hmac_sha256_final(&combined_measurements);
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
  // 1K should be enough for the largest certificate perso LTV object.
  const size_t kBufferSize = 1024;
  uint8_t buffer[kBufferSize];

  // Read first word of the certificate perso LTV object (contains the size).
  perso_tlv_object_header_t objh;
  uint16_t obj_size;
  TRY(flash_ctrl_info_read(page, offset, 1, buffer));
  memcpy(&objh, buffer, sizeof(perso_tlv_object_header_t));
  PERSO_TLV_GET_FIELD(Objh, Size, objh, &obj_size);

  // Validate the perso LTV object size.
  if (obj_size == 0) {
    LOG_ERROR(
        "Inconsistent certificate perso LTV object header %02x %02x at "
        "page:offset %x:%x",
        buffer[0], buffer[1], page->base_addr, offset);
    return DATA_LOSS();
  }
  if (obj_size > sizeof(buffer)) {
    LOG_ERROR("Bad certificate perso LTV object size %d at page:offset %x:%x",
              obj_size, page->base_addr, offset);
    return DATA_LOSS();
  }
  if ((obj_size + offset) > FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
    LOG_ERROR("Cert size overflow (%d + %d) page %x:%x", obj_size, offset,
              page->base_addr, offset);
    return DATA_LOSS();
  }

  // Read the entire perso LTV object from flash and parse it.
  perso_tlv_cert_obj_t cert_obj;
  TRY(flash_ctrl_info_read(page, offset, util_size_to_words(obj_size), buffer));
  TRY(perso_tlv_get_cert_obj(buffer, kBufferSize, &cert_obj));

  hmac_sha256_update(cert_obj.cert_body_p, cert_obj.cert_body_size);

  if (size) {
    *size = obj_size;
  }

  return OK_STATUS();
}

static status_t hash_all_certs(void) {
  uint32_t cert_obj_size;
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
      TRY(hash_certificate(curr_layout.info_page, page_offset, &cert_obj_size));
      page_offset += util_size_to_words(cert_obj_size) * sizeof(uint32_t);
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
  // We copy over the UDS endorsement key ID to an SHA256 digest type, since
  // this is the format of key IDs generated on-dice.
  memcpy(uds_endorsement_key_id.digest, certgen_inputs.dice_auth_key_key_id,
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
  // Note:
  // - We do not measure HwCfg0 as this is the Device ID, which is already
  //   mixed into the keyladder directly via hardware channels.
  // - We pre-calculate the OTP measurement of CreatorSwCfg and OwnerSwCfg
  //   partitions using expected values for fields not yet provisioned. This
  //   ensures consistent measurements throughout personalization.
  TRY(measure_otp_partition(kOtpPartitionCreatorSwCfg,
                            &otp_creator_sw_cfg_measurement,
                            /*use_expected_values=*/true));
  TRY(measure_otp_partition(kOtpPartitionOwnerSwCfg,
                            &otp_owner_sw_cfg_measurement,
                            /*use_expected_values=*/true));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthCodesign,
                            &otp_rot_creator_auth_codesign_measurement,
                            /*use_expected_values=*/false));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthState,
                            &otp_rot_creator_auth_state_measurement,
                            /*use_expected_values=*/false));

  /*****************************************************************************
   * DICE certificates.
   ****************************************************************************/
  size_t curr_cert_size = 0;

  // Generate UDS keys and (TBS) cert.
  curr_cert_size = kUdsMaxTbsSizeBytes;
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyUds, &uds_pubkey_id,
                                     &curr_pubkey));
  memcpy(&uds_pubkey, &curr_pubkey, sizeof(ecdsa_p256_public_key_t));
  TRY(otbn_boot_attestation_key_save(kDiceKeyUds.keygen_seed_idx,
                                     kDiceKeyUds.type,
                                     *kDiceKeyUds.keymgr_diversifier));

  // Build the certificate in a temp buffer, use all_certs for that.
  TRY(dice_uds_tbs_cert_build(
      &otp_creator_sw_cfg_measurement, &otp_owner_sw_cfg_measurement,
      &otp_rot_creator_auth_codesign_measurement,
      &otp_rot_creator_auth_state_measurement, &uds_key_ids, &curr_pubkey,
      all_certs, &curr_cert_size));
  // DO NOT CHANGE THE "UDS" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  uds_offset = perso_blob_to_host.next_free;
  TRY(perso_tlv_push_cert_to_perso_blob(
      "UDS",
      /*needs_endorsement=*/kDiceCertFormat == kDiceCertFormatX509TcbInfo,
      kDiceCertFormat, all_certs, curr_cert_size, &perso_blob_to_host));
  LOG_INFO("Generated UDS certificate.");

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
  // DO NOT CHANGE THE "CDI_0" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  TRY(perso_tlv_push_cert_to_perso_blob("CDI_0", /*needs_endorsement=*/false,
                                        kDiceCertFormat, all_certs,
                                        curr_cert_size, &perso_blob_to_host));
  LOG_INFO("Generated CDI_0 certificate.");

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
  // DO NOT CHANGE THE "CDI_1" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  TRY(perso_tlv_push_cert_to_perso_blob("CDI_1", /*needs_endorsement=*/false,
                                        kDiceCertFormat, all_certs,
                                        curr_cert_size, &perso_blob_to_host));
  LOG_INFO("Generated CDI_1 certificate.");

  return OK_STATUS();
}

// Returns how much data is left in the perso blob receive buffer (i.e., `body`
// field). Useful when scanning the receive buffer containing perso LTV objects.
static size_t max_available(void) {
  if (perso_blob_from_host.next_free > sizeof(perso_blob_from_host.body))
    return 0;  // This could never happen, but just in case.

  return sizeof(perso_blob_from_host.body) - perso_blob_from_host.next_free;
}

/**
 * Find the next certificate perso LTV object in the receive perso buffer and
 * copy it to the passed in location.
 *
 * @param dest Pointer to pointer in the destination buffer; this function
 *             advances the pointer by the size of the copied certificate perso
 *             LTV object.
 * @param free_room Pointer to the size of the destination buffer; this function
 *                  reduces the size of the buffer by the size of the copied
 *                  certificate perso LTV object.
 */
static status_t extract_next_cert(uint8_t **dest, size_t *free_room) {
  // A just in case sanity check that the next free location in the perso blob
  // data buffer is at the end of the buffer.
  if (perso_blob_from_host.next_free > sizeof(perso_blob_from_host.body)) {
    return INTERNAL();  // Something is really screwed up.
  }

  // Scan the received buffer until the next endorsed cert is found.
  while (perso_blob_from_host.num_objs != 0) {
    perso_tlv_cert_obj_t block;

    // Extract the next perso LTV object, aborting if it is not a certificate.
    rom_error_t err = perso_tlv_get_cert_obj(
        perso_blob_from_host.body + perso_blob_from_host.next_free,
        max_available(), &block);
    switch (err) {
      case kErrorOk:
        break;
      case kErrorPersoTlvCertObjNotFound: {
        // The object found is not a certificate. Skip to next perso LTV object.
        perso_blob_from_host.next_free += block.obj_size;
        perso_blob_from_host.num_objs--;
        continue;
      }
      default:
        return INTERNAL();
    }

    // Check there is enough room in the destination buffer to copy the
    // certificate perso LTV object.
    if (*free_room < block.obj_size)
      return RESOURCE_EXHAUSTED();

    // Copy the certificate object to the destination buffer.
    uint8_t *dest_p = *dest;
    memcpy(dest_p, block.obj_p, block.obj_size);
    LOG_INFO("Copied %s certificate", block.name);

    // Advance destination buffer pointer and reduce free space counter.
    *dest = dest_p + block.obj_size;
    *free_room = *free_room - block.obj_size;

    // Advance pointer to next perso LTV object in the receive buffer.
    perso_blob_from_host.next_free += block.obj_size;
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
   * All certificates are ordered in a buffer (all_certs) according to the order
   * in which they will be written to flash. That order is:
   * 1. UDS cert
   * 2. CDI_0 cert
   * 3. CDI_1 cert
   * 4. Provision Extension certs
   ****************************************************************************/
  // We start scanning the perso LTV buffer we received from the host from the
  // beginnging. We assume that the endorsed UDS cert is the first certificate
  // in the buffer (even if preceeded by other types of perso LTV objects).
  perso_blob_from_host.next_free = 0;
  // Location where the next cert perso LTV object will be copied to in the
  // `all_certs` buffer.
  uint8_t *next_cert = all_certs;
  // How much room left in the destination (`all_certs`) buffer.
  size_t free_room = sizeof(all_certs);
  // Helper structure caching certificate information from a certificate perso
  // LTV object.
  perso_tlv_cert_obj_t block;

  // CWT DICE doesn't need host to endorse any certificate for it, so all
  // payload are in the "perso_blob_to_host".
  // Default to this setting, and move to X509 setting if the flag is set.
  size_t cert_offsets[3] = {uds_offset, cdi_0_offset, cdi_1_offset};
  size_t cert_offsets_count = 3;
  if (kDiceCertFormat == kDiceCertFormatX509TcbInfo) {
    // Exract the UDS cert perso LTV object.
    TRY(extract_next_cert(&next_cert, &free_room));
    // Extract the two CDI cert perso LTV objects which were endorsed on-device
    // and sent to the host.
    cert_offsets[0] = cert_offsets[1];
    cert_offsets[1] = cert_offsets[2];
    cert_offsets_count = 2;
  }
  // Extract the cert perso LTV objects which were endorsed on-device and send
  // to the host.
  for (size_t i = 0; i < cert_offsets_count; i++) {
    size_t offset = cert_offsets[i];
    TRY(perso_tlv_get_cert_obj(perso_blob_to_host.body + offset,
                               sizeof(perso_blob_to_host.body) - offset,
                               &block));
    if (block.obj_size > free_room)
      return RESOURCE_EXHAUSTED();

    memcpy(next_cert, block.obj_p, block.obj_size);
    LOG_INFO("Copied %s certificate", block.name);
    next_cert += block.obj_size;
    free_room -= block.obj_size;
  }

  // Extract the remaining cert perso LTV objects received from the host.
  while (perso_blob_from_host.num_objs)
    TRY(extract_next_cert(&next_cert, &free_room));

  /*****************************************************************************
   * Save Certificates to Flash.
   ****************************************************************************/
  // This is where the certificates to be copied are stored, each one encoded as
  // a perso LTV object. Reset the `next_cert` pointer and `free_room` size.
  next_cert = all_certs;
  free_room = sizeof(all_certs);
  for (size_t i = 0; i < ARRAYSIZE(cert_flash_layout); i++) {
    const cert_flash_info_layout_t curr_layout = cert_flash_layout[i];
    uint32_t page_offset = 0;

    // Skip the page if it is not in use.
    if (!curr_layout.used) {
      continue;
    }

    // This is a bit brittle, but we expect the sum of {layout}.num_certs values
    // in the following flash layout sections to be equal to the number of
    // endorsed extension certificates received from the host.
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      // Extract the cert block from the `all_certs` buffer.
      TRY(perso_tlv_get_cert_obj(next_cert, free_room, &block));
      // Round up the size to the nearest word boundary.
      uint32_t cert_size_words = util_size_to_words(block.obj_size);
      uint32_t cert_size_bytes_ru = cert_size_words * sizeof(uint32_t);
      if ((page_offset + cert_size_bytes_ru) >
          FLASH_CTRL_PARAM_BYTES_PER_PAGE) {
        LOG_ERROR("%s %s certificate did not fit into the info page.",
                  curr_layout.group_name, block.name);
        return OUT_OF_RANGE();
      }
      TRY(flash_ctrl_info_write(curr_layout.info_page, page_offset,
                                cert_size_words, next_cert));
      LOG_INFO("Imported %s %s certificate.", curr_layout.group_name,
               block.name);
      page_offset += cert_size_bytes_ru;
      next_cert += block.obj_size;

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

/**
 * Compare the OTP measurement used during certificate generation with the OTP
 * measurment calculated from the final OTP values. Ensure that the UDS
 * certificate was generated using the correct OTP values.
 */
static status_t check_otp_measurement_pre_lock(hmac_digest_t *measurement,
                                               otp_partition_t partition) {
  hmac_digest_t final_measurement;
  TRY(measure_otp_partition(partition, &final_measurement,
                            /*use_expected_values=*/false));

  TRY_CHECK(final_measurement.digest[1] == measurement->digest[1]);
  TRY_CHECK(final_measurement.digest[0] == measurement->digest[0]);
  return OK_STATUS();
}

/**
 * Compare the OTP measurement used during certificate generation with the
 * digest stored in the OTP. Ensure that the UDS certificate was generated using
 * the correct OTP values.
 */
static status_t check_otp_measurement_post_lock(hmac_digest_t *measurement,
                                                uint32_t offset) {
  uint64_t expected_digest = otp_read64(offset);
  uint32_t digest_hi = expected_digest >> 32;
  uint32_t digest_lo = expected_digest & UINT32_MAX;
  TRY_CHECK(digest_hi == measurement->digest[1]);
  TRY_CHECK(digest_lo == measurement->digest[0]);
  return OK_STATUS();
}

static status_t finalize_otp_partitions(void) {
  // TODO(#21554): Complete the provisioning of the root keys and key policies.

  TRY(check_next_slot_bootable());

  // Complete the provisioning of OTP OwnerSwCfg partition.
  if (!status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET));
    TRY(check_otp_measurement_pre_lock(&otp_owner_sw_cfg_measurement,
                                       kOtpPartitionOwnerSwCfg));
    TRY(manuf_individualize_device_owner_sw_cfg_lock(&otp_ctrl));
  }
  TRY(check_otp_measurement_post_lock(
      &otp_owner_sw_cfg_measurement,
      OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_OFFSET));

  // Complete the provisioning of OTP CreatorSwCfg partition.
  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_CREATOR_SW_CFG_MANUF_STATE_OFFSET));
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN_OFFSET));
    TRY(check_otp_measurement_pre_lock(&otp_creator_sw_cfg_measurement,
                                       kOtpPartitionCreatorSwCfg));
    TRY(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
  }
  TRY(check_otp_measurement_post_lock(
      &otp_creator_sw_cfg_measurement,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_OFFSET));

  return OK_STATUS();
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
      .flash_ctrl_handle = &flash_ctrl_state,
      .uds_pubkey = &uds_pubkey,
      .uds_pubkey_id = &uds_pubkey_id,
      .otp_creator_sw_cfg_measurement = &otp_creator_sw_cfg_measurement,
      .otp_owner_sw_cfg_measurement = &otp_owner_sw_cfg_measurement,
      .otp_rot_creator_auth_codesign_measurement =
          &otp_rot_creator_auth_codesign_measurement,
      .otp_rot_creator_auth_state_measurement =
          &otp_rot_creator_auth_state_measurement};
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

  CHECK_STATUS_OK(finalize_otp_partitions());
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  LOG_INFO("Personalization done.");

  return true;
}
