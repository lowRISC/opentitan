// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice_chain.h"

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/static_dice_cdi_0.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
static dice_storage_page_t dice_page;

static cert_key_id_pair_t dice_chain_cdi_0_key_ids = (cert_key_id_pair_t){
    .endorsement = &static_dice_cdi_0.uds_pubkey_id,
    .cert = &static_dice_cdi_0.cdi_0_pubkey_id,
};

rom_error_t dice_chain_attestation_silicon(void) {
  // Initialize the entropy complex and KMAC for key manager operations.
  // Note: `OTCRYPTO_OK.value` is equal to `kErrorOk` but we cannot add a static
  // assertion here since its definition is not an integer constant expression.
  HARDENED_RETURN_IF_ERROR(
      (rom_error_t)entropy_complex_init(kHardenedBoolFalse).value);
  HARDENED_RETURN_IF_ERROR(kmac_keymgr_configure());

  // Set keymgr reseed interval. Start with the maximum value to avoid
  // entropy complex contention during the boot process.
  const uint16_t kScKeymgrEntropyReseedInterval = UINT16_MAX;
  sc_keymgr_entropy_reseed_interval_set(kScKeymgrEntropyReseedInterval);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioEntropyReseedIntervalSet);

  // ROM sets the SW binding values for the first key stage (CreatorRootKey) but
  // does not initialize the key manager. Advance key manager state twice to
  // transition to the CreatorRootKey state.
  RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateInit));

  // Generate UDS keys.
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateCreatorRootKey));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyUds, &static_dice_cdi_0.uds_pubkey_id,
      &static_dice_cdi_0.uds_pubkey));

  return kErrorOk;
}

rom_error_t dice_chain_attestation_creator(
    keymgr_binding_value_t *rom_ext_measurement,
    const manifest_t *rom_ext_manifest) {
  // Save UDS key for signing next stage cert.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyUds.keygen_seed_idx, kDiceKeyUds.type,
      *kDiceKeyUds.keymgr_diversifier));

  // Generate CDI_0 attestation keys and (potentially) update certificate.
  keymgr_binding_value_t seal_binding_value = {
      .data = {rom_ext_manifest->identifier, 0}};
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);
  HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_int_advance(
      /*sealing_binding=*/&seal_binding_value,
      /*attest_binding=*/rom_ext_measurement,
      rom_ext_manifest->max_key_version));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyCdi0, &static_dice_cdi_0.cdi_0_pubkey_id,
      &static_dice_cdi_0.cdi_0_pubkey));

  // Check if the current CDI_0 cert is valid.
  uint64_t expected_cdi0_id = read_64(static_dice_cdi_0.cdi_0_pubkey_id.digest);

  uint64_t cached_cdi0_id;
  RETURN_IF_ERROR(dice_storage_get_cdi_0_id(&cached_cdi0_id));

  bool cache_valid = cached_cdi0_id == expected_cdi0_id;

  if (!cache_valid) {
    // Update the cert page buffer.
    static_dice_cdi_0.cert_size = sizeof(static_dice_cdi_0.cert_data);
    HARDENED_RETURN_IF_ERROR(dice_cdi_0_cert_build(
        (hmac_digest_t *)rom_ext_measurement->data,
        rom_ext_manifest->security_version, &dice_chain_cdi_0_key_ids,
        &static_dice_cdi_0.uds_pubkey, &static_dice_cdi_0.cdi_0_pubkey,
        static_dice_cdi_0.cert_data, &static_dice_cdi_0.cert_size));
  }

  sc_keymgr_sw_binding_unlock_wait();

  return kErrorOk;
}

rom_error_t dice_chain_rom_ext_check(void) {
  // If a CDI_0 certificate is issued, the entire cache will be rebuilt, so
  // the digest check can be skipped.
  if (static_dice_cdi_0.cert_size != 0) {
    return kErrorOk;
  }

  RETURN_IF_ERROR(dice_storage_load_page(&dice_page));

  rom_error_t status = dice_storage_check_digest(&dice_page);
  if (status != kErrorOk) {
    dbg_printf("warning: corrupted page; erasing\r\n");
    RETURN_IF_ERROR(flash_ctrl_info_erase(&kFlashCtrlInfoPageDiceCerts,
                                          kFlashCtrlEraseTypePage));
    return status;
  }
  return kErrorOk;
}

rom_error_t dice_chain_attestation_owner(
    const manifest_t *owner_manifest, keymgr_binding_value_t *bl0_measurement,
    hmac_digest_t *owner_measurement, hmac_digest_t *owner_history_hash,
    keymgr_binding_value_t *sealing_binding, owner_app_domain_t key_domain) {
  // Save CDI_0 key for signing next stage cert.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier));

  // Local variables for CDI_1 key generation and cert building
  hmac_digest_t subject_pubkey_id;
  ecdsa_p256_public_key_t subject_pubkey;
  cert_key_id_pair_t key_ids = {
      .endorsement = &static_dice_cdi_0.cdi_0_pubkey_id,
      .cert = &subject_pubkey_id,
  };

  // Generate CDI_1 attestation keys and (potentially) update certificate.
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);
  static_assert(
      sizeof(hmac_digest_t) == sizeof(keymgr_binding_value_t),
      "Expect the keymgr binding value to be the same size as a sha256 digest");

  // Aggregate the owner firmware (BL0) measurement and the ownership
  // measurement into a single attestation measurment.  The attestation
  // measurement is used to initialize the keymgr.
  hmac_digest_t attest_measurement;
  hmac_sha256_configure(false);
  hmac_sha256_start();
  hmac_sha256_update(bl0_measurement, sizeof(*bl0_measurement));
  hmac_sha256_update(owner_measurement, sizeof(*owner_measurement));
  hmac_sha256_process();
  hmac_sha256_final(&attest_measurement);

  HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_advance(
      /*sealing_binding=*/sealing_binding,
      /*attest_binding=*/(keymgr_binding_value_t *)&attest_measurement,
      owner_manifest->max_key_version));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyCdi1, &subject_pubkey_id, &subject_pubkey));

  // Load page to dice_page.
  RETURN_IF_ERROR(dice_storage_load_page(&dice_page));

  uint64_t expected_cdi1_id = read_64(subject_pubkey_id.digest);

  bool cache_valid = (static_dice_cdi_0.cert_size == 0 &&
                      dice_page.cdi_1_key_id == expected_cdi1_id);

  if (!cache_valid) {
    dbg_puts("info: DICE cert cache miss; updating\r\n");

    // If CDI_0 in RAM is valid, copy it to dice_page.
    if (static_dice_cdi_0.cert_size != 0) {
      dice_storage_slot_init(&kDiceStorageCdi0Ecdsa, &dice_page);
      memcpy(dice_storage_slot_data(&kDiceStorageCdi0Ecdsa, &dice_page),
             static_dice_cdi_0.cert_data, static_dice_cdi_0.cert_size);
      dice_storage_set_cert_size(&kDiceStorageCdi0Ecdsa,
                                 static_dice_cdi_0.cert_size, &dice_page);
      dice_page.cdi_0_key_id =
          read_64(static_dice_cdi_0.cdi_0_pubkey_id.digest);
    }

    // Generate CDI_1 directly into dice_page.
    dice_storage_slot_init(&kDiceStorageCdi1Ecdsa, &dice_page);
    uint8_t *cdi1_cert_data_ptr =
        dice_storage_slot_data(&kDiceStorageCdi1Ecdsa, &dice_page);
    size_t generated_cdi1_size = kDiceStorageCdi1Ecdsa.data_size;
    HARDENED_RETURN_IF_ERROR(dice_cdi_1_cert_build(
        (hmac_digest_t *)bl0_measurement, owner_measurement, owner_history_hash,
        owner_manifest->security_version, key_domain, &key_ids,
        &static_dice_cdi_0.cdi_0_pubkey, &subject_pubkey, cdi1_cert_data_ptr,
        &generated_cdi1_size));
    dice_storage_set_cert_size(&kDiceStorageCdi1Ecdsa, generated_cdi1_size,
                               &dice_page);
    dice_page.cdi_1_key_id = expected_cdi1_id;

    // Calculate and update digest.
    dice_storage_digest_page(&dice_page, &dice_page.digest);

    // Flush page to flash.
    RETURN_IF_ERROR(dice_storage_flush_page(&dice_page));
  }

  sc_keymgr_sw_binding_unlock_wait();

  // Save CDI_1 key for endorsing next stage cert.
  // TODO: Remove this save once all ownersw are migrated to derive the key
  // on their own. This save is added only for compatibility.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier));
  return kErrorOk;
}

rom_error_t dice_chain_init(void) {
  // Configure DICE certificate flash info page and buffer it into RAM.
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  // Configure factory certs page.
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageFactoryCerts,
                          kCertificateInfoPageCfg);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageFactoryCerts);
  return kErrorOk;
}
