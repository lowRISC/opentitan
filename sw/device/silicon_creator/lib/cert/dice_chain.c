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

#include "hw/top/flash_ctrl_regs.h"  // Generated.

enum {
  kFlashPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
};

/**
 * Defines a class for parsing and building the DICE cert chain.
 *
 * All of the fields in this struct should be considered private, and users
 * should call the public `dice_chain_*` functions instead.
 */
typedef struct dice_chain {
  /**
   * RAM buffer that mirrors the DICE cert chain in a flash page.
   */
  dice_page_t page;

  /**
   * Indicate whether `page` needs to be written back to flash.
   */
  hardened_bool_t data_dirty;

  /**
   * The amount of bytes in `page.data` that has been processed.
   */
  size_t tail_offset;

  /**
   * Indicate the info page currently buffered in `page`.
   * This is used to skip unnecessary read ops.
   */
  const flash_ctrl_info_page_t *info_page;

  /**
   * Id pair which points to the endorsement and cert ids below.
   */
  cert_key_id_pair_t key_ids;

  /**
   * Public key id for signing endorsement cert.
   */
  hmac_digest_t endorsement_pubkey_id;

  /**
   * Subject public key id of the current cert.
   */
  hmac_digest_t subject_pubkey_id;

  /**
   * Subject public key contents of the current cert.
   */
  ecdsa_p256_public_key_t subject_pubkey;

  /**
   * Scratch buffer for constructing CDI certs.
   */
  uint8_t scratch_cert[kDicePageDataSize];

  /**
   * The current tlv cert the builder is processing.
   */
  perso_tlv_cert_obj_t cert_obj;

  /**
   * The version of the perso blob.
   */
  perso_blob_version_t blob_version;

  /**
   * Indicate whether the `cert_obj` is valid for the current `subject_pubkey`.
   */
  hardened_bool_t cert_valid;

} dice_chain_t;

static dice_chain_t dice_chain;

static cert_key_id_pair_t dice_chain_cdi_0_key_ids = (cert_key_id_pair_t){
    .endorsement = &static_dice_cdi_0.uds_pubkey_id,
    .cert = &static_dice_cdi_0.cdi_0_pubkey_id,
};

// Get the size of the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
OT_NOINLINE
static size_t dice_chain_get_tail_size(void) {
  HARDENED_CHECK_GE(sizeof(dice_chain.page.data), dice_chain.tail_offset);
  return sizeof(dice_chain.page.data) - dice_chain.tail_offset;
}

// Get the pointer to the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
static uint8_t *dice_chain_get_tail_buffer(void) {
  return &dice_chain.page.data[dice_chain.tail_offset];
}

// Cleanup stale `cert_obj` data and mark it as invalid.
static void dice_chain_reset_cert_obj(void) {
  memset(&dice_chain.cert_obj, 0, sizeof(dice_chain.cert_obj));
  dice_chain.cert_valid = kHardenedBoolFalse;
}

/**
 * Increments the DICE cert buffer offset to the next TLV object.
 * (ensuring to round up to the 64-bit flash word offset to prevent potential
 * ECC issues).
 */
static void dice_chain_next_cert_obj(void) {
  // Round up to next flash word for next perso TLV object offset.
  size_t cert_size = dice_chain.cert_obj.obj_size;

  // The cert_size is only 12-bit, which won't cause unsigned overflow.
  cert_size = util_size_to_words(cert_size) * sizeof(uint32_t);
  cert_size = util_round_up_to(cert_size, 3);

  // Jump to the next object.
  dice_chain.tail_offset += cert_size;

  // Post-check for the buffer boundary.
  HARDENED_CHECK_LE(dice_chain.tail_offset, sizeof(dice_chain.page.data));

  dice_chain_reset_cert_obj();
}

/**
 * Load the tlv cert obj from the tail buffer and check if it's valid.
 *
 * This method will update the `dice_chain` fields of current certificate:
 *   * `cert_obj` will be all zeros if not TLV cert entry is found.
 *   * `cert_valid` will only be set to true if name and pubkey matches.
 *
 * @param name The cert name to match.
 * @param name_size Size in byte of the `name` argument. Caller has to ensure it
 * is smaller than kCrthNameSizeFieldMask.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_load_cert_obj(const char *name,
                                            size_t name_size) {
  rom_error_t err = perso_tlv_get_cert_obj(
      dice_chain_get_tail_buffer(), dice_chain_get_tail_size(),
      dice_chain.blob_version, &dice_chain.cert_obj);
  if (err != kErrorOk) {
    // Cleanup the stale value if error.
    dice_chain_reset_cert_obj();

    // If the cert is not found or corrupted, continue and allow the ROM_EXT
    // to generate an identity certificate for the current DICE stage. The
    // error is not fatal, and the cert obj has been marked as invalid.
    return kErrorOk;
  }

  // Check if this cert is what we are looking for. The name and type (X.509 vs
  // CWT) should match.
  const perso_tlv_object_type_t kExpectedCertType =
      kDiceCertFormat == kDiceCertFormatX509TcbInfo ? kPersoObjectTypeX509Cert
                                                    : kPersoObjectTypeCwtCert;
  if (name == NULL || memcmp(dice_chain.cert_obj.name, name, name_size) != 0 ||
      kExpectedCertType != dice_chain.cert_obj.obj_type) {
    // Name unmatched, keep the cert_obj but mark it as invalid.
    dice_chain.cert_valid = kHardenedBoolFalse;
    return kErrorOk;
  }

  // Check if the subject pubkey is matched. `cert_valid` will be set to false
  // if unmatched.
  RETURN_IF_ERROR(dice_cert_check_valid(
      &dice_chain.cert_obj, &dice_chain.subject_pubkey_id,
      &dice_chain.subject_pubkey, &dice_chain.cert_valid));

  return kErrorOk;
}

// Skip the TLV entry if the name matches.
static rom_error_t dice_chain_skip_cert_obj(const char *name,
                                            size_t name_size) {
  RETURN_IF_ERROR(dice_chain_load_cert_obj(NULL, 0));
  if (memcmp(dice_chain.cert_obj.name, name, name_size) == 0) {
    dice_chain_next_cert_obj();
  }
  return kErrorOk;
}

// Load the certificate data from flash to RAM buffer.
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_load_flash(
    const flash_ctrl_info_page_t *info_page) {
  // Skip reload if it's already buffered.
  if (dice_chain.info_page == info_page) {
    dice_chain.tail_offset = 0;
    return kErrorOk;
  }

  // We are switching to a different page, flush changes (if dirty) first.
  RETURN_IF_ERROR(dice_chain_flush_flash());

  // Read in a DICE certificate(s) page.
  static_assert(sizeof(dice_chain.page) == kFlashPageSize,
                "Invalid dice_chain buffer size");
  RETURN_IF_ERROR(flash_ctrl_info_read_zeros_on_read_error(
      info_page, /*offset=*/0,
      /*word_count=*/kFlashPageSize / sizeof(uint32_t), &dice_chain.page));

  // Resets the flash page status.
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.tail_offset = 0;
  dice_chain.info_page = info_page;
  dice_chain_reset_cert_obj();

  // Detect the version of the blob stored in flash.
  size_t offset = 0;
  RETURN_IF_ERROR(perso_tlv_get_blob_version(
      dice_chain.page.data, sizeof(dice_chain.page.data),
      &dice_chain.blob_version, &offset));
  dice_chain.tail_offset = offset;

  return kErrorOk;
}

// Add the hash digest to the last of the page.
static rom_error_t dice_chain_seal_page(void) {
  // Hash the entire page before the digest.
  hmac_sha256(dice_chain.page.data, sizeof(dice_chain.page.data),
              &dice_chain.page.digest);

  // The page is going to be updated.
  dice_chain.data_dirty = kHardenedBoolTrue;

  return kErrorOk;
}

// Push the certificate to the tail with TLV header.
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_push_cert(const char *name, const uint8_t *cert,
                                        const size_t cert_size) {
  // The data is going to be updated, mark it as dirty and clear the tail.
  dice_chain.data_dirty = kHardenedBoolTrue;

  // Invalidate all the remaining certificates in the tail buffer.
  memset(dice_chain_get_tail_buffer(), 0, dice_chain_get_tail_size());

  // Encode the certificate to the tail buffer.
  size_t cert_page_left = dice_chain_get_tail_size();
  perso_tlv_object_type_t cert_type =
      kDiceCertFormat == kDiceCertFormatX509TcbInfo ? kPersoObjectTypeX509Cert
                                                    : kPersoObjectTypeCwtCert;
  RETURN_IF_ERROR(perso_tlv_cert_obj_build(
      name, cert_type, cert, cert_size, dice_chain.blob_version,
      dice_chain_get_tail_buffer(), &cert_page_left));

  // Move the offset to the new tail.
  RETURN_IF_ERROR(perso_tlv_get_cert_obj(
      dice_chain_get_tail_buffer(), dice_chain_get_tail_size(),
      dice_chain.blob_version, &dice_chain.cert_obj));
  dice_chain_next_cert_obj();
  return kErrorOk;
}

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

  // Save UDS key for signing next stage cert.
  RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyUds.keygen_seed_idx, kDiceKeyUds.type,
      *kDiceKeyUds.keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_chain_attestation_creator(
    keymgr_binding_value_t *rom_ext_measurement,
    const manifest_t *rom_ext_manifest) {
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
  } else {
    // Replace UDS with CDI_0 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
        *kDiceKeyCdi0.keymgr_diversifier));
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
  } else {
    // Replace CDI_0 with CDI_1 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
        *kDiceKeyCdi1.keymgr_diversifier));
  }

  sc_keymgr_sw_binding_unlock_wait();
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
