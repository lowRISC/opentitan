// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
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
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/manuf/base/flash_info_permissions.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/base/personalize_ext.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/individualize_sw_cfg.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

enum {
  /**
   * Size of the largest OTP partition to be measured.
   */
  kDiceMeasuredOtpPartitionMaxSizeIn32bitWords =
      (OTP_CTRL_PARAM_OWNER_SW_CFG_SIZE -
       OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_SIZE) /
      sizeof(uint32_t),
};

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
static dif_gpio_t gpio;
static dif_lc_ctrl_t lc_ctrl;
static dif_otp_ctrl_t otp_ctrl;
static dif_pinmux_t pinmux;
static dif_rstmgr_t rstmgr;

// ATE Indicator GPIOs.
static const dif_gpio_pin_t kGpioPinTestStart = 0;
static const dif_gpio_pin_t kGpioPinTestDone = 1;
static const dif_gpio_pin_t kGpioPinTestError = 2;
static const dif_gpio_pin_t kGpioPinSpiConsoleTxReady = 3;
static const dif_gpio_pin_t kGpioPinSpiConsoleRxReady = 4;

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false,
                        .console.putbuf_buffered = true,
                        .silence_console_prints = true,
                        .console_tx_indicator.enable = true,
                        .console_tx_indicator.spi_console_tx_ready_mio =
                            kTopEarlgreyPinmuxMioOutIoa5,
                        .console_tx_indicator.spi_console_tx_ready_gpio =
                            kGpioPinSpiConsoleTxReady);

/**
 * Certificates flash info page layout.
 */
// 1K should be enough for the largest certificate perso LTV object.
enum { kBufferSize = 1024 };
static cert_flash_info_layout_t cert_flash_layout[] = {
    {
        // The DICE UDS cert is placed on this page since it must remain stable
        // post manufacturing. This page should never be erased by ROM_EXT, nor
        // owner firmware.
        .used = true,
        .need_digest = true,
        .group_name = "FACTORY",
        .info_page = &kFlashCtrlInfoPageFactoryCerts,
        .num_certs = 1,
    },
    {
        .used = true,
        .need_digest = true,
        .group_name = "DICE",
        .info_page = &kFlashCtrlInfoPageDiceCerts,
        .num_certs = 2,
    },
    // These flash info pages can be used by provisioning extensions to store
    // additional certificates SKU owners may desire to provision.
    {
        .used = false,
        .need_digest = false,
        .group_name = "Ext0",
        .info_page = &kFlashCtrlInfoPageOwnerReserved6,
        .num_certs = 0,
    },
    {
        .used = false,
        .need_digest = false,
        .group_name = "Ext1",
        .info_page = &kFlashCtrlInfoPageOwnerReserved7,
        .num_certs = 0,
    },
};

/**
 * Ownership initialization function.
 */
OT_WEAK rom_error_t sku_creator_owner_init(boot_data_t *bootdata) {
  OT_DISCARD(bootdata);
  LOG_ERROR("No ownership initialization");
  return kErrorOk;
}

/**
 * Pushes the hash of the personalization firmware to the perso blob.
 */
static status_t log_self_hash(perso_blob_t *blob_to_host) {
  TRY(perso_tlv_push_object_to_perso_blob(
      kPersoObjectTypePersoSha256Hash, boot_measurements.rom_ext.data,
      sizeof(keymgr_binding_value_t), kPersoBlobVersionV0, blob_to_host));
  return OK_STATUS();
}

/*
 * Return a pointer to the ROM_EXT manifest located in the slot a.
 */
static const manifest_t *rom_ext_manifest_a_get(void) {
  return (const manifest_t *)TOP_EARLGREY_EFLASH_BASE_ADDR;
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
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  TRY(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
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
 * Erase all of the owner's INFO pages so that they're in a known state.
 */
static status_t erase_owner_info_pages(owner_config_t *config) {
  const flash_ctrl_info_page_t *pages[] = {
      &kFlashCtrlInfoPageOwnerReserved0, &kFlashCtrlInfoPageOwnerReserved1,
      &kFlashCtrlInfoPageOwnerReserved2, &kFlashCtrlInfoPageOwnerReserved3,
      &kFlashCtrlInfoPageOwnerReserved4, &kFlashCtrlInfoPageOwnerReserved5,
      &kFlashCtrlInfoPageOwnerReserved6, &kFlashCtrlInfoPageOwnerReserved7,
  };

  // First, initialize all of the owner INFO pages with ECC & Scrambling.
  for (size_t i = 0; i < ARRAYSIZE(pages); ++i) {
    flash_ctrl_cfg_t cfg = {
        .scrambling = kMultiBitBool4True,
        .ecc = kMultiBitBool4True,
        .he = kMultiBitBool4False,
    };
    flash_ctrl_info_cfg_set(pages[i], cfg);
  }

  // Next, overwrite the INFO page configuration for those pages defined
  // in the owner block.
  TRY(owner_block_info_apply(config->info));

  // Finally, erase each page.
  for (size_t i = 0; i < ARRAYSIZE(pages); ++i) {
    flash_ctrl_perms_t perms = {
        .read = kMultiBitBool4True,
        .write = kMultiBitBool4True,
        .erase = kMultiBitBool4True,
    };
    flash_ctrl_info_perms_set(pages[i], perms);
    TRY(flash_ctrl_info_erase(pages[i], kFlashCtrlEraseTypePage));
  }

  return OK_STATUS();
}

/**
 * Helper function to compute measurements of various OTP partitions that are to
 * be included in attestation certificates.
 */
static status_t measure_otp_partition(otp_partition_t partition,
                                      hmac_digest_t *measurement,
                                      bool use_expected_values,
                                      uint32_t *otp_state) {
  // Compute the digest.
  otp_dai_read(partition, /*relative_address=*/0, otp_state,
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

  uint32_t *otp_state_ptr = otp_state;
  size_t otp_state_size = kOtpPartitions[partition].size;
  if (partition == kOtpPartitionCreatorSwCfg) {
    // Note: we purposely exclude the AST configuration data field of this
    // partition from the digest calculation. See
    // sw/device/silicon_creator/manuf/lib/util.c for why.
    otp_state_ptr = &otp_state[OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_SIZE /
                               sizeof(uint32_t)];
    otp_state_size -= OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_CFG_SIZE;
  }
  hmac_sha256(otp_state_ptr, otp_state_size, measurement);

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
    base_printf("Bootstrap requested.\n");
    wait_for_interrupt();
  }

  // Provision OTP Secret2 partition and flash info pages 1, 2, and 4 (keymgr
  // and DICE keygen seeds).
  if (!status_ok(manuf_personalize_device_secrets_check(&otp_ctrl))) {
    lc_token_hash_t token_hash;
    // Wait for the host to send the RMA unlock token hash over the console.
    base_printf("Waiting For RMA Unlock Token Hash ...\n");
    TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, true));
    TRY(UJSON_WITH_CRC(ujson_deserialize_lc_token_hash_t, uj, &token_hash));
    TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, false));

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
 * Sets the attestation and sealing binding to all zeros.
 *
 * The attestation binding (and subsequently CDI_0) will be updated later when
 * the ROM_EXT boots for the first time.
 */
static void compute_keymgr_owner_int_binding(
    keymgr_binding_value_t *sealing_binding_value,
    keymgr_binding_value_t *attestation_binding_value) {
  memset(attestation_binding_value->data, 0, kDiceMeasurementSizeInBytes);
  // In the silicon_creator stage, we set the sealing binding to the
  // manifest->identifier of the ROM_EXT stage.
  memset(sealing_binding_value->data, 0, kDiceMeasurementSizeInBytes);
  sealing_binding_value->data[0] = CHIP_ROM_EXT_IDENTIFIER;
}

/**
 * Sets the attestation binding to all zeros as it (and subsequently CDI_1) will
 * be updated later when the ROM_EXT boots for the first time.
 *
 * The sealing binding value is set to the TEST application key domain.
 */
static void compute_keymgr_owner_binding(
    keymgr_binding_value_t *sealing_binding_value,
    keymgr_binding_value_t *attestation_binding_value) {
  memset(attestation_binding_value->data, 0, kDiceMeasurementSizeInBytes);
  // We expect the owner to use a Application Key binding  of
  // {`prod`, 0, ... }.
  memset(sealing_binding_value->data, 0, kDiceMeasurementSizeInBytes);
  sealing_binding_value->data[0] = kOwnerAppDomainProd;
}

typedef struct cert_scratch_buffer {
  uint8_t buffer[kBufferSize];
} __attribute__((aligned(4))) cert_scratch_buffer_t;

typedef struct aligned_dice_storage_page {
  dice_storage_page_t page;
} __attribute__((aligned(8))) aligned_dice_storage_page_t;

/**
 * Read a certificate from the passed in location in a flash INFO page and hash
 * its contents on the existing sha256 hashing stream. Determine the actual
 * certificate size from its ASN1 header.
 *
 * If the caller passed a pointer, save there the certificate size.
 */
static status_t hash_certificate(const flash_ctrl_info_page_t *page,
                                 size_t offset, size_t *size,
                                 cert_scratch_buffer_t *cert_buffer) {
  memset(cert_buffer->buffer, 0, sizeof(cert_buffer->buffer));

  // Read first 16 bytes of the certificate perso LTV object to determine size.
  alignas(uint32_t) uint8_t head[16];
  TRY(flash_ctrl_info_read(page, offset, util_size_to_words(sizeof(head)),
                           head));
  uint32_t obj_size = perso_tlv_object_size(head, sizeof(head));

  // Validate the perso LTV object size.
  if (obj_size == 0) {
    LOG_ERROR(
        "Inconsistent certificate perso LTV object header %02x %02x at "
        "page:offset %x:%x",
        head[0], head[1], page->base_addr, offset);
    return DATA_LOSS();
  }
  if (obj_size > sizeof(cert_buffer->buffer)) {
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
  perso_tlv_cert_obj_view_t cert_obj;
  TRY(flash_ctrl_info_read(page, offset, util_size_to_words(obj_size),
                           cert_buffer->buffer));
  TRY(perso_tlv_get_cert_obj_view(cert_buffer->buffer, kBufferSize, &cert_obj));
  hmac_sha256_update(cert_obj.cert_body_p, cert_obj.cert_body_size);

  if (size) {
    *size = obj_size;
  }

  return OK_STATUS();
}

static status_t hash_all_certs(cert_scratch_buffer_t *cert_buffer) {
  uint32_t cert_obj_size;
  hmac_sha256_init();

  // Push all certificates into the hash.
  for (size_t i = 0; i < ARRAYSIZE(cert_flash_layout); i++) {
    const cert_flash_info_layout_t curr_layout = cert_flash_layout[i];
    // Skip the page if it is not in use.
    if (!curr_layout.used) {
      continue;
    }

    uint32_t page_offset = 0;

    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      TRY(hash_certificate(curr_layout.info_page, page_offset, &cert_obj_size,
                           cert_buffer));
      page_offset += util_size_to_words(cert_obj_size) * sizeof(uint32_t);
      page_offset = util_round_up_to(page_offset, 3);
    }
  }

  return OK_STATUS();
}

/**
 * Crank the keymgr to produce the DICE attestation keys and certificates.
 */
static status_t personalize_gen_dice_certificates(
    ujson_t *uj, perso_blob_t *blob_to_host,
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    manuf_certgen_inputs_t *certgen_inputs, ecdsa_p256_public_key_t *uds_pubkey,
    hmac_digest_t *uds_pubkey_id, uint8_t *all_certs, size_t all_certs_size,
    size_t *uds_offset, size_t *cdi_0_offset, size_t *cdi_1_offset,
    keymgr_binding_value_t *sealing_binding_value,
    keymgr_binding_value_t *attestation_binding_value,
    ecdsa_p256_public_key_t *curr_pubkey, ecdsa_p256_public_key_t *cdi_0_pubkey,
    uint32_t *otp_state) {
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
  base_printf("Waiting for certificate inputs ...\n");
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, true));
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, certgen_inputs));
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, false));

  hmac_digest_t uds_endorsement_key_id = {0};
  // We copy over the UDS endorsement key ID to an SHA256 digest type, since
  // this is the format of key IDs generated on-dice.
  memcpy(uds_endorsement_key_id.digest, certgen_inputs->dice_auth_key_key_id,
         kCertKeyIdSizeInBytes);

  // Initialize entropy complex / KMAC for key manager operations.
  TRY(entropy_complex_init(kHardenedBoolFalse));
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
                            otp_creator_sw_cfg_measurement,
                            /*use_expected_values=*/true, otp_state));
  TRY(measure_otp_partition(kOtpPartitionOwnerSwCfg,
                            otp_owner_sw_cfg_measurement,
                            /*use_expected_values=*/true, otp_state));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthCodesign,
                            otp_rot_creator_auth_codesign_measurement,
                            /*use_expected_values=*/false, otp_state));
  TRY(measure_otp_partition(kOtpPartitionRotCreatorAuthState,
                            otp_rot_creator_auth_state_measurement,
                            /*use_expected_values=*/false, otp_state));

  /*****************************************************************************
   * DICE certificates.
   ****************************************************************************/
  size_t curr_cert_size = 0;

  // Generate UDS keys and (TBS) cert.
  curr_cert_size = kUdsMaxTbsSizeBytes;
  if (all_certs_size < curr_cert_size) {
    return RESOURCE_EXHAUSTED();
  }
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyUds, uds_pubkey_id, curr_pubkey));
  memcpy(uds_pubkey, curr_pubkey, sizeof(ecdsa_p256_public_key_t));
  TRY(otbn_boot_attestation_key_save(kDiceKeyUds.keygen_seed_idx,
                                     kDiceKeyUds.type,
                                     *kDiceKeyUds.keymgr_diversifier));

  const cert_key_id_pair_t uds_key_ids = {
      .endorsement = &uds_endorsement_key_id,
      .cert = uds_pubkey_id,
  };

  // Build the certificate in a temp buffer, use all_certs for that.
  TRY(dice_uds_tbs_cert_build(
      otp_creator_sw_cfg_measurement, otp_owner_sw_cfg_measurement,
      otp_rot_creator_auth_codesign_measurement,
      otp_rot_creator_auth_state_measurement, &uds_key_ids, curr_pubkey,
      all_certs, &curr_cert_size));
  // DO NOT CHANGE THE "UDS" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  *uds_offset = blob_to_host->next_free;
  TRY(perso_tlv_push_cert_to_perso_blob(
      "UDS",
      /*needs_endorsement=*/kDiceCertFormat == kDiceCertFormatX509TcbInfo,
      kDiceCertFormat, all_certs, curr_cert_size, kPersoBlobVersionV0,
      blob_to_host));

  // After we have cranked the keymgr to the CreatorRootKey (UDS) stage, we now
  // can initialize and seal the ownership block.
  ownership_seal_init();

  const static hmac_digest_t zero_digest = {.digest = {0, 0, 0, 0, 0, 0, 0, 0}};
  hmac_digest_t cdi_0_pubkey_id = {0};
  hmac_digest_t cdi_1_pubkey_id = {0};

  // Generate CDI_0 keys and cert.
  TRY(otbn_boot_attestation_key_save(kDiceKeyUds.keygen_seed_idx,
                                     kDiceKeyUds.type,
                                     *kDiceKeyUds.keymgr_diversifier));
  curr_cert_size = kCdi0MaxCertSizeBytes;
  if (all_certs_size < curr_cert_size) {
    return RESOURCE_EXHAUSTED();
  }
  compute_keymgr_owner_int_binding(sealing_binding_value,
                                   attestation_binding_value);
  TRY(sc_keymgr_owner_int_advance(sealing_binding_value,
                                  attestation_binding_value,
                                  /*max_key_version=*/0));
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyCdi0, &cdi_0_pubkey_id,
                                     curr_pubkey));
  const cert_key_id_pair_t cdi_0_key_ids = {
      .endorsement = uds_pubkey_id,
      .cert = &cdi_0_pubkey_id,
  };

  memcpy(cdi_0_pubkey, curr_pubkey, sizeof(ecdsa_p256_public_key_t));
  TRY(dice_cdi_0_cert_build(&zero_digest, 0, &cdi_0_key_ids, uds_pubkey,
                            curr_pubkey, all_certs, &curr_cert_size));
  *cdi_0_offset = blob_to_host->next_free;
  // DO NOT CHANGE THE "CDI_0" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  TRY(perso_tlv_push_cert_to_perso_blob(
      "CDI_0", /*needs_endorsement=*/false, kDiceCertFormat, all_certs,
      curr_cert_size, kPersoBlobVersionV0, blob_to_host));

  // Generate CDI_1 keys and cert.
  TRY(otbn_boot_attestation_key_save(kDiceKeyCdi0.keygen_seed_idx,
                                     kDiceKeyCdi0.type,
                                     *kDiceKeyCdi0.keymgr_diversifier));
  curr_cert_size = kCdi1MaxCertSizeBytes;
  if (all_certs_size < curr_cert_size) {
    return RESOURCE_EXHAUSTED();
  }
  compute_keymgr_owner_binding(sealing_binding_value,
                               attestation_binding_value);
  TRY(sc_keymgr_owner_advance(sealing_binding_value, attestation_binding_value,
                              /*max_key_version=*/0));
  TRY(otbn_boot_cert_ecc_p256_keygen(kDiceKeyCdi1, &cdi_1_pubkey_id,
                                     curr_pubkey));
  const cert_key_id_pair_t cdi_1_key_ids = {
      .endorsement = &cdi_0_pubkey_id,
      .cert = &cdi_1_pubkey_id,
  };
  TRY(dice_cdi_1_cert_build(&zero_digest, &zero_digest, &zero_digest, 0,
                            kOwnerAppDomainProd, &cdi_1_key_ids, cdi_0_pubkey,
                            curr_pubkey, all_certs, &curr_cert_size));
  *cdi_1_offset = blob_to_host->next_free;
  // DO NOT CHANGE THE "CDI_1" STRING BELOW with modifying the `dice_cert_names`
  // collection in sw/host/provisioning/ft_lib/src/lib.rs.
  TRY(perso_tlv_push_cert_to_perso_blob(
      "CDI_1", /*needs_endorsement=*/false, kDiceCertFormat, all_certs,
      curr_cert_size, kPersoBlobVersionV0, blob_to_host));

  return OK_STATUS();
}

static status_t compute_tbs_was_hmac(perso_blob_t *blob_to_host) {
  // Read out the WAS from flash.
  hmac_key_t was;
  static_assert(
      kFlashInfoFieldWaferAuthSecretSizeIn32BitWords == kHmacKeyNumWords,
      "WAS size expected to be same size as HMAC-SHA256 key.");
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret.page,
      kFlashInfoFieldWaferAuthSecret.bank,
      kFlashInfoFieldWaferAuthSecret.partition, kFlashInfoPage3ReadPermissions,
      /*offset=*/NULL));
  TRY(manuf_flash_info_field_read(
      &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret, was.key,
      kFlashInfoFieldWaferAuthSecretSizeIn32BitWords));

  // Compute HMAC of TBS certs with WAS as the key.
  // HSMs and host tooling will compute an HMAC in big endian format, so we do
  // the same to make the comparison easier.
  hmac_hmac_sha256_init(was, /*big_endian_digest=*/true);
  uint8_t *tlv_buf = blob_to_host->body;
  uint32_t obj_size;
  perso_tlv_object_type_t obj_type;
  perso_tlv_cert_obj_view_t cert_obj;
  for (size_t i = 0; i < blob_to_host->num_objs; ++i) {
    size_t rem_size =
        sizeof(blob_to_host->body) - (size_t)(tlv_buf - blob_to_host->body);
    obj_type = perso_tlv_object_type(tlv_buf, rem_size);
    obj_size = perso_tlv_object_size(tlv_buf, rem_size);
    if (obj_type == kPersoObjectTypeX509Tbs) {
      TRY(perso_tlv_get_cert_obj_view(tlv_buf, rem_size, &cert_obj));
      hmac_sha256_update(cert_obj.cert_body_p, cert_obj.cert_body_size);
    }
    tlv_buf += obj_size;
  }
  hmac_sha256_process();
  hmac_digest_t digest;
  hmac_sha256_final(&digest);

  // Push hash into perso blob.
  TRY(perso_tlv_push_object_to_perso_blob(kPersoObjectTypeWasTbsHmac,
                                          digest.digest, kHmacDigestNumBytes,
                                          kPersoBlobVersionV0, blob_to_host));

  // Read complete device ID and push into perso blob. The host will need the
  // device ID to reconstruct the WAS.
  uint32_t device_id[kHwCfgDeviceIdSizeIn32BitWords] = {0};
  TRY(otp_ctrl_testutils_dai_read32_array(&otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                          kHwCfgDeviceIdOffset, device_id,
                                          ARRAYSIZE(device_id)));
  TRY(perso_tlv_push_object_to_perso_blob(kPersoObjectTypeDeviceId, device_id,
                                          kHwCfgDeviceIdSizeInBytes,
                                          kPersoBlobVersionV0, blob_to_host));

  return OK_STATUS();
}

static status_t boot_data_cfg_initialize(void) {
  // Configure the boot data OTP word.
  if (!status_ok(manuf_individualize_device_flash_info_boot_data_cfg_check(
          &otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl,
        OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG_OFFSET));
  }

  // Loads the boot data configuration from OTP.
  flash_ctrl_cfg_t boot_data_cfg = flash_ctrl_boot_data_cfg_get();

  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4True,
  };

  // Erase the BootData pages. This is necessary to ensure that the owner
  // block is written to a clean page and to avoid ECC errors in the
  // next boot.
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageBootData0, perm);
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageBootData1, perm);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageBootData0, boot_data_cfg);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageBootData1, boot_data_cfg);

  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageBootData0,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageBootData1,
                            kFlashCtrlEraseTypePage));

  return OK_STATUS();
}

static status_t install_owner(owner_config_t *config,
                              owner_application_keyring_t *keyring) {
  // Get the boot_data; installing the owner will write it back with the
  // ownership_state set to LockedOwner.
  boot_data_t boot_data;
  TRY(boot_data_read(kLcStateProd, &boot_data));

  // Initialize the ownership-related flash pages.
  flash_ctrl_perms_t perm = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_cfg_t cfg = {
      .scrambling = kMultiBitBool4True,
      .ecc = kMultiBitBool4True,
      .he = kMultiBitBool4False,
  };
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot0, perm);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageOwnerSlot0, cfg);
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageOwnerSlot1, perm);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageOwnerSlot1, cfg);

  // Initializes the boot data flash configuration in OTP, and erases the boot
  // data pages to avoid integrity errors in the next boot.
  // `sku_creator_owner_init` will write the owner block to the flash.
  TRY(boot_data_cfg_initialize());

  // Initialize ownership.  This will write the owner block into OwnerSlot0 and
  // set the ownership_state to LockedOwner.  The first boot of the ROM_EXT
  // will create a redundanty copy in OwnerSlot1.
  TRY(sku_creator_owner_init(&boot_data));
  TRY(owner_block_parse(&owner_page[0],
                        /*check_only=*/kHardenedBoolFalse, config, keyring));
  return OK_STATUS();
}

// Returns how much data is left in the perso blob receive buffer (i.e., `body`
// field). Useful when scanning the receive buffer containing perso LTV objects.
static size_t max_available(const perso_blob_t *blob) {
  if (blob->next_free > sizeof(blob->body))
    return 0;  // This could never happen, but just in case.

  return sizeof(blob->body) - blob->next_free;
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
static status_t extract_next_cert(uint8_t **dest, size_t *free_room,
                                  perso_blob_t *blob_from_host) {
  // A just in case sanity check that the next free location in the perso blob
  // data buffer is at the end of the buffer.
  if (blob_from_host->next_free > sizeof(blob_from_host->body)) {
    return INTERNAL();  // Something is really screwed up.
  }

  // Scan the received buffer until the next endorsed cert is found.
  while (blob_from_host->num_objs != 0) {
    perso_tlv_cert_obj_view_t block;

    // Extract the next perso LTV object, aborting if it is not a certificate.
    rom_error_t err = perso_tlv_get_cert_obj_view(
        blob_from_host->body + blob_from_host->next_free,
        max_available(blob_from_host), &block);
    switch (err) {
      case kErrorOk:
        break;
      case kErrorPersoTlvCertObjNotFound: {
        // The object found is not a certificate. Skip to next perso LTV object.
        blob_from_host->next_free += block.obj_size;
        blob_from_host->num_objs--;
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

    // Advance destination buffer pointer and reduce free space counter.
    *dest = dest_p + block.obj_size;
    *free_room = *free_room - block.obj_size;

    // Advance pointer to next perso LTV object in the receive buffer.
    blob_from_host->next_free += block.obj_size;
    blob_from_host->num_objs--;
    return OK_STATUS();
  }

  return OK_STATUS();
}

static status_t write_cert_to_dice_page(const cert_flash_info_layout_t *layout,
                                        perso_tlv_cert_obj_view_t *block,
                                        uint8_t *cert_data,
                                        uint32_t page_offset,
                                        uint32_t cert_write_size_bytes,
                                        dice_storage_page_t *const dice_page) {
  base_printf("Importing %s cert to %s ...\n", block->name, layout->group_name);
  if ((page_offset + cert_write_size_bytes) > sizeof(dice_page->data)) {
    LOG_ERROR("%s %s certificate did not fit into the info page.",
              layout->group_name, block->name);
    return OUT_OF_RANGE();
  }

  // The page will be zero-padded between obj_size to cert_write_size_bytes.
  TRY_CHECK(block->obj_size <= cert_write_size_bytes);

  // Copy the actual certificate data into the cert buffer.
  memcpy(dice_page->data + page_offset, cert_data, block->obj_size);

  return OK_STATUS();
}

static status_t write_digest_to_dice_page(
    const cert_flash_info_layout_t *layout, dice_storage_page_t *dice_page) {
  base_printf("Digesting %s page ...\n", layout->group_name);

  hmac_sha256(dice_page, sizeof(*dice_page) - sizeof(dice_page->digest),
              &(dice_page->digest));

  return OK_STATUS();
}

static status_t personalize_endorse_certificates(
    ujson_t *uj, const perso_blob_t *blob_to_host, perso_blob_t *blob_from_host,
    uint8_t *all_certs, const size_t all_certs_size, const size_t uds_offset,
    const size_t cdi_0_offset, const size_t cdi_1_offset,
    aligned_dice_storage_page_t *dice_page) {
  /*****************************************************************************
   * Certificate Export and Endorsement.
   ****************************************************************************/
  // Export the certificates to the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  base_printf("Exporting TBS certificates ...\n");
  RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_perso_blob_t, uj,
                        blob_to_host, kPersoBlobSerializedMaxSize);

  // Import endorsed certificates from the provisioning appliance.
  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  base_printf("Importing endorsed certificates ...\n");
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, true));
  TRY(ujson_deserialize_perso_blob_t(uj, blob_from_host));
  TRY(dif_gpio_write(&gpio, kGpioPinSpiConsoleRxReady, false));

  blob_from_host->next_free = 0;
  const size_t num_objs_in_blob_from_host = blob_from_host->num_objs;

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
  // We start scanning the received perso LTV buffer we received from the host.
  // We assume that the endorsed UDS cert is the first certificate
  // in the buffer (even if preceeded by other types of perso LTV objects).
  //
  // Location where the next cert perso LTV object will be copied to in the
  // `all_certs` buffer.
  uint8_t *next_cert = all_certs;
  // How much room left in the destination (`all_certs`) buffer.
  size_t free_room = all_certs_size;
  // Helper structure caching certificate information from a certificate perso
  // LTV object.
  perso_tlv_cert_obj_view_t block;

  // CWT DICE doesn't need host to endorse any certificate for it, so all
  // payload are in the "blob_to_host".
  // Default to this setting, and move to X509 setting if the flag is set.
  size_t cert_offsets[3] = {uds_offset, cdi_0_offset, cdi_1_offset};
  size_t cert_offsets_count = 3;
  if (kDiceCertFormat == kDiceCertFormatX509TcbInfo) {
    // Exract the UDS cert perso LTV object.
    TRY(extract_next_cert(&next_cert, &free_room, blob_from_host));
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
    TRY(perso_tlv_get_cert_obj_view(blob_to_host->body + offset,
                                    sizeof(blob_to_host->body) - offset,
                                    &block));
    if (block.obj_size > free_room)
      return RESOURCE_EXHAUSTED();
    memcpy(next_cert, block.obj_p, block.obj_size);
    next_cert += block.obj_size;
    free_room -= block.obj_size;
  }

  // Extract the remaining cert perso LTV objects received from the host.
  while (blob_from_host->num_objs)
    TRY(extract_next_cert(&next_cert, &free_room, blob_from_host));

  /*****************************************************************************
   * Save Certificates to Flash.
   ****************************************************************************/
  // This is where the certificates to be copied are stored, each one encoded as
  // a perso LTV object. Reset the `next_cert` pointer and `free_room` size.
  next_cert = all_certs;
  free_room = all_certs_size;
  for (size_t i = 0; i < ARRAYSIZE(cert_flash_layout); i++) {
    const cert_flash_info_layout_t curr_layout = cert_flash_layout[i];
    uint32_t page_offset = 0;

    // Skip the page if it is not in use.
    if (!curr_layout.used) {
      continue;
    }

    memset(&dice_page->page, 0, sizeof(dice_page->page));

    // This is a bit brittle, but we expect the sum of {layout}.num_certs values
    // in the following flash layout sections to be equal to the number of
    // endorsed extension certificates received from the host.
    for (size_t j = 0; j < curr_layout.num_certs; j++) {
      // Extract the cert block from the `all_certs` buffer.
      TRY(perso_tlv_get_cert_obj_view(next_cert, free_room, &block));
      // Round up the size to the nearest word boundary.
      uint32_t cert_size_words = util_size_to_words(block.obj_size);
      uint32_t cert_size_bytes_ru = cert_size_words * sizeof(uint32_t);
      TRY(write_cert_to_dice_page(&curr_layout, &block, next_cert, page_offset,
                                  cert_size_bytes_ru, &dice_page->page));
      page_offset += cert_size_bytes_ru;
      next_cert += block.obj_size;

      // Each certificate must be 8 bytes aligned (flash word size).
      page_offset = util_round_up_to(page_offset, 3);
    }

    if (curr_layout.need_digest) {
      TRY(write_digest_to_dice_page(&curr_layout, &dice_page->page));
    }

    TRY(flash_ctrl_info_write(curr_layout.info_page, /*page_offset=*/0,
                              util_size_to_words(sizeof(dice_page->page)),
                              &dice_page->page));
  }

  blob_from_host->num_objs = num_objs_in_blob_from_host;

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  base_printf("Finished importing certificates.\n");

  return OK_STATUS();
}

/**
 * Compare the OTP measurement used during certificate generation with the OTP
 * measurment calculated from the final OTP values. Ensure that the UDS
 * certificate was generated using the correct OTP values.
 */
static status_t check_otp_measurement_pre_lock(const hmac_digest_t *measurement,
                                               otp_partition_t partition,
                                               uint32_t *otp_state) {
  hmac_digest_t final_measurement;
  TRY(measure_otp_partition(partition, &final_measurement,
                            /*use_expected_values=*/false, otp_state));

  TRY_CHECK(final_measurement.digest[1] == measurement->digest[1]);
  TRY_CHECK(final_measurement.digest[0] == measurement->digest[0]);
  return OK_STATUS();
}

/**
 * Compare the OTP measurement used during certificate generation with the
 * digest stored in the OTP. Ensure that the UDS certificate was generated using
 * the correct OTP values.
 */
static status_t check_otp_measurement_post_lock(
    const hmac_digest_t *measurement, uint32_t offset) {
  uint64_t expected_digest = otp_read64(offset);
  uint32_t digest_hi = expected_digest >> 32;
  uint32_t digest_lo = expected_digest & UINT32_MAX;
  TRY_CHECK(digest_hi == measurement->digest[1]);
  TRY_CHECK(digest_lo == measurement->digest[0]);
  return OK_STATUS();
}

static status_t finalize_otp_partitions(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement, uint32_t *otp_state) {
  TRY(check_next_slot_bootable());

  // Complete the provisioning of OTP OwnerSwCfg partition.
  if (!status_ok(manuf_individualize_device_owner_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_BOOTSTRAP_DIS_OFFSET));
    TRY(check_otp_measurement_pre_lock(otp_owner_sw_cfg_measurement,
                                       kOtpPartitionOwnerSwCfg, otp_state));
    TRY(manuf_individualize_device_owner_sw_cfg_lock(&otp_ctrl));
  }
  TRY(check_otp_measurement_post_lock(
      otp_owner_sw_cfg_measurement, OTP_CTRL_PARAM_OWNER_SW_CFG_DIGEST_OFFSET));

  // Complete the provisioning of OTP CreatorSwCfg partition.
  if (!status_ok(manuf_individualize_device_creator_sw_cfg_check(&otp_ctrl))) {
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_CREATOR_SW_CFG_MANUF_STATE_OFFSET));
    TRY(manuf_individualize_device_field_cfg(
        &otp_ctrl, OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN_OFFSET));
    TRY(check_otp_measurement_pre_lock(otp_creator_sw_cfg_measurement,
                                       kOtpPartitionCreatorSwCfg, otp_state));
    TRY(manuf_individualize_device_creator_sw_cfg_lock(&otp_ctrl));
  }
  TRY(check_otp_measurement_post_lock(
      otp_creator_sw_cfg_measurement,
      OTP_CTRL_PARAM_CREATOR_SW_CFG_DIGEST_OFFSET));

  return OK_STATUS();
}

static status_t configure_ate_gpio_indicators(void) {
  // IOA6 / GPIO4 is for SPI console RX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa6,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinSpiConsoleRxReady));
  // IOA5 / GPIO3 is for SPI console TX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa5,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinSpiConsoleTxReady));
  // IOA0 / GPIO2 is for error reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa0,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestError));
  // IOA1 / GPIO1 is for test done reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa1,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestDone));
  // IOA4 / GPIO0 is for test start reporting.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa4,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinTestStart));
  TRY(dif_gpio_output_set_enabled_all(&gpio, 0x1f));  // Enable first 5 GPIOs.
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));    // Intialize all to 0.
  return OK_STATUS();
}

typedef struct perso_pre_endorse_data {
  manuf_certgen_inputs_t certgen_inputs;
  ecdsa_p256_public_key_t uds_pubkey;

  /*
   * Keymgr binding values.
   */
  keymgr_binding_value_t attestation_binding_value;
  keymgr_binding_value_t sealing_binding_value;

  // Temporary buffer to store EC-DSA public keys during DICE cert generation
  ecdsa_p256_public_key_t curr_pubkey;
  // Temporary buffer to store CDI0 public key after it is generated and until
  // CDI1 certificate is endorsed
  ecdsa_p256_public_key_t cdi_0_pubkey;
} perso_pre_endorse_data_t;

typedef struct perso_post_endorse_data {
  // Temporary buffer to read endorsed cert into when hashing it
  cert_scratch_buffer_t cert_buffer;
  // Temporary buffer to populate dice page data before actually writing to
  // flash pages
  aligned_dice_storage_page_t dice_page;
} perso_post_endorse_data_t;

typedef enum perso_stage {
  PERSO_STAGE_PRE_ENDORSE,
  PERSO_STAGE_POST_ENDORSE,
} perso_stage_t;

// NOTE: This approach to `stage_specific_data` data assumes that firmware will
// not maintain any references to data from any prior stages. For example: the
// firmware will not maintain pointer to the `uds_pubkey` while it is available
// in the pre-endorsement stage, and then dereference that pointer in the post
// endorsement stage.
typedef struct perso_stage_specific_data {
  perso_stage_t stage;
  union {
    perso_pre_endorse_data_t pre_endorse_data;
    perso_post_endorse_data_t post_endorse_data;
  } data;
} perso_stage_specific_data_t;

typedef struct perso_stages_shared_data {
  perso_blob_t blob_to_host;    // Perso data device => host.
  perso_blob_t blob_from_host;  // Perso data host => device.

  // Used to store individual certs during pre-endorse stage, and store all
  // certs during post-endorse stage
  uint8_t all_certs[8192];

  uint32_t otp_state[kDiceMeasuredOtpPartitionMaxSizeIn32bitWords];
} perso_stages_shared_data_t;

typedef struct perso_data {
  perso_stage_specific_data_t stage_specific_data;
  perso_stages_shared_data_t stages_shared_data;
} perso_data_t;

static status_t provision(ujson_t *uj) {
  // Provision OTP, flash secrets, certs, and install the first owner.
  TRY(lc_ctrl_testutils_operational_state_check(&lc_ctrl));
  TRY(personalize_otp_and_flash_secrets(uj));

  hmac_digest_t otp_creator_sw_cfg_measurement = {0};
  hmac_digest_t otp_owner_sw_cfg_measurement = {0};
  hmac_digest_t uds_pubkey_id = {0};
  size_t uds_offset = {0};
  size_t cdi_0_offset = {0};
  size_t cdi_1_offset = {0};

  static perso_data_t perso_data;

  {
    perso_data.stage_specific_data.stage = PERSO_STAGE_PRE_ENDORSE;
    perso_pre_endorse_data_t *pre_endorse_data =
        &perso_data.stage_specific_data.data.pre_endorse_data;
    hmac_digest_t otp_rot_creator_auth_codesign_measurement = {0};
    hmac_digest_t otp_rot_creator_auth_state_measurement = {0};

    TRY(personalize_gen_dice_certificates(
        uj, &perso_data.stages_shared_data.blob_to_host,
        &otp_creator_sw_cfg_measurement, &otp_owner_sw_cfg_measurement,
        &otp_rot_creator_auth_codesign_measurement,
        &otp_rot_creator_auth_state_measurement,
        &pre_endorse_data->certgen_inputs, &pre_endorse_data->uds_pubkey,
        &uds_pubkey_id, perso_data.stages_shared_data.all_certs,
        sizeof(perso_data.stages_shared_data.all_certs), &uds_offset,
        &cdi_0_offset, &cdi_1_offset, &pre_endorse_data->sealing_binding_value,
        &pre_endorse_data->attestation_binding_value,
        &pre_endorse_data->curr_pubkey, &pre_endorse_data->cdi_0_pubkey,
        perso_data.stages_shared_data.otp_state));
    owner_config_t owner_config;
    owner_application_keyring_t owner_keyring = {0};
    TRY(install_owner(&owner_config, &owner_keyring));

    // Erase all of the owner-reserved INFO pages before performing any
    // DICE or owner-customized certificate generation.
    TRY(erase_owner_info_pages(&owner_config));

    personalize_extension_pre_endorse_t pre_endorse = {
        .uj = uj,
        .certgen_inputs = &perso_data.stage_specific_data.data.pre_endorse_data
                               .certgen_inputs,
        .perso_blob_to_host = &perso_data.stages_shared_data.blob_to_host,
        .cert_flash_layout = cert_flash_layout,
        .flash_ctrl_handle = &flash_ctrl_state,
        .uds_pubkey = &pre_endorse_data->uds_pubkey,
        .uds_pubkey_id = &uds_pubkey_id,
        .otp_creator_sw_cfg_measurement = &otp_creator_sw_cfg_measurement,
        .otp_owner_sw_cfg_measurement = &otp_owner_sw_cfg_measurement,
        .otp_rot_creator_auth_codesign_measurement =
            &otp_rot_creator_auth_codesign_measurement,
        .otp_rot_creator_auth_state_measurement =
            &otp_rot_creator_auth_state_measurement};
    TRY(personalize_extension_pre_cert_endorse(&pre_endorse));
    TRY(compute_tbs_was_hmac(&perso_data.stages_shared_data.blob_to_host));
    TRY(log_self_hash(&perso_data.stages_shared_data.blob_to_host));
  }

  {
    // Technically, the post endorse stage starts inside
    // `personalize_endorse_certificates`, but this structure is starting to use
    // the post endorse fields here
    perso_data.stage_specific_data.stage = PERSO_STAGE_POST_ENDORSE;
    perso_post_endorse_data_t *post_endorse_data =
        &perso_data.stage_specific_data.data.post_endorse_data;
    // Endorse TBS certs and install in flash.
    TRY(personalize_endorse_certificates(
        uj, &perso_data.stages_shared_data.blob_to_host,
        &perso_data.stages_shared_data.blob_from_host,
        perso_data.stages_shared_data.all_certs,
        sizeof(perso_data.stages_shared_data.all_certs), uds_offset,
        cdi_0_offset, cdi_1_offset, &post_endorse_data->dice_page));
    TRY(hash_all_certs(&post_endorse_data->cert_buffer));
    personalize_extension_post_endorse_t post_endorse = {
        .uj = uj,
        .perso_blob_from_host = &perso_data.stages_shared_data.blob_from_host,
        .cert_flash_layout = cert_flash_layout};
    TRY(personalize_extension_post_cert_endorse(&post_endorse));

    // Check the hash of all perso objects with the host to confirm integrity of
    // the transmission / provisioning operations.
    serdes_sha256_hash_t hash;
    hmac_sha256_process();
    hmac_sha256_final((hmac_digest_t *)&hash);

    TRY(RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_serdes_sha256_hash_t,
                              uj, &hash, kSerdesSha256HashSerializedMaxSize));

    // Complete any remaining OTP programming.
    TRY(finalize_otp_partitions(&otp_creator_sw_cfg_measurement,
                                &otp_owner_sw_cfg_measurement,
                                perso_data.stages_shared_data.otp_state));
  }

  return OK_STATUS();
}

bool test_main(void) {
  // Log our boot status in the lifecycle token registers.
  const manifest_t *self = rom_ext_manifest_a_get();
  lifecycle_claim(kMultiBitBool8True);
  lifecycle_set_status(kLifecycleStatusWordRomExtVersion, self->version_minor);
  lifecycle_set_status(kLifecycleStatusWordRomExtSecVersion,
                       self->security_version);
  lifecycle_set_status(kLifecycleStatusWordOwnerVersion, 0);
  lifecycle_set_status(kLifecycleStatusWordDeviceStatus,
                       kLifecycleDeviceStatusPersoStart);
  lifecycle_claim(kMultiBitBool8False);

  // Unconditionally disable the watchdog timer.
  // This is needed to avoid a watchdog reset if enabled in the ROM.
  watchdog_disable();

  // Enable peripherals, ATE GPIO indicators, and the SPI console.
  CHECK_STATUS_OK(peripheral_handles_init());
  pinmux_testutils_init(&pinmux);
  CHECK_STATUS_OK(configure_ate_gpio_indicators());
  CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestStart, true));
  CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolFalse));
  ujson_t uj = ujson_ottf_console();

  // Read the reset reason directly from the RSTMGR.
  // This is needed to clear the reset reason before the first call to
  // `personalize_otp_and_flash_secrets()`, which will reset the device.
  uint32_t reason = rstmgr_reason_get();
  if (reason != 0) {
    rstmgr_reason_clear(reason);
  }

  // Execute personalization provisioning sequence.
  status_t result = provision(&uj);
  if (!status_ok(result)) {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestError, true));
  } else {
    CHECK_DIF_OK(dif_gpio_write(&gpio, kGpioPinTestDone, true));
  }

  // DO NOT CHANGE THE BELOW STRING without modifying the host code in
  // sw/host/provisioning/ft_lib/src/lib.rs
  base_printf("Personalization done.\n");

  return true;
}
