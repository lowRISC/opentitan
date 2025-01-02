// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/dice_chain.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "flash_ctrl_regs.h"  // Generated.

enum {
  /**
   * The size of the scratch buffer that is large enough for constructing the
   * CDI certs.
   */
  kScratchCertSizeBytes =
      (kCdi0MaxCertSizeBytes > kCdi1MaxCertSizeBytes ? kCdi0MaxCertSizeBytes
                                                     : kCdi1MaxCertSizeBytes),
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
  uint8_t data[FLASH_CTRL_PARAM_BYTES_PER_PAGE];

  /**
   * Indicate whether `data` needs to be written back to flash.
   */
  hardened_bool_t data_dirty;

  /**
   * The amount of bytes in `data` that has been processed.
   */
  size_t tail_offset;

  /**
   * Indicate the info page currently buffered in `data`.
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
  uint8_t scratch_cert[kScratchCertSizeBytes];

  /**
   * The current tlv cert the builder is processing.
   */
  perso_tlv_cert_obj_t cert_obj;

  /**
   * Indicate whether the `cert_obj` is valid for the current `subject_pubkey`.
   */
  hardened_bool_t cert_valid;

} dice_chain_t;

static dice_chain_t dice_chain;

// Get the size of the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
static size_t dice_chain_get_tail_size(void) {
  HARDENED_CHECK_GE(sizeof(dice_chain.data), dice_chain.tail_offset);
  return sizeof(dice_chain.data) - dice_chain.tail_offset;
}

// Get the pointer to the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
static uint8_t *dice_chain_get_tail_buffer(void) {
  return &dice_chain.data[dice_chain.tail_offset];
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

  // Pre-check to prevent the alignment op from unsigned overflow.
  HARDENED_CHECK_LE(cert_size, dice_chain_get_tail_size());
  cert_size = util_size_to_words(cert_size) * sizeof(uint32_t);
  cert_size = util_round_up_to(cert_size, 3);
  // Post-check for the buffer boundary.
  HARDENED_CHECK_LE(cert_size, dice_chain_get_tail_size());

  // Jump to the next object.
  dice_chain.tail_offset += cert_size;
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
 * @param name_size Size in byte of the `name` argument.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_load_cert_obj(const char *name,
                                            size_t name_size) {
  rom_error_t err =
      perso_tlv_get_cert_obj(dice_chain_get_tail_buffer(),
                             dice_chain_get_tail_size(), &dice_chain.cert_obj);

  if (err != kErrorOk) {
    // Cleanup the stale value if error.
    dice_chain_reset_cert_obj();
  }

  if (err == kErrorPersoTlvCertObjNotFound) {
    // If the cert is not found it is because we are running on a sim or FPGA
    // platform, or the device has not yet been provisioned. Continue, and let
    // the ROM_EXT generate an identity certificate for the current DICE stage.
    // The error is not fatal, and the cert obj has been marked as invalid.
    return kErrorOk;
  }

  HARDENED_RETURN_IF_ERROR(err);

  // Check if this cert is what we are looking for.
  HARDENED_CHECK_LE(name_size, sizeof(dice_chain.cert_obj.name));
  if (name == NULL || memcmp(dice_chain.cert_obj.name, name, name_size) != 0) {
    // Name unmatched, keep the cert_obj but mark it as invalid.
    dice_chain.cert_valid = kHardenedBoolFalse;
    return kErrorOk;
  }

  // Check if the subject pubkey is matched. `cert_valid` will be set to false
  // if unmatched.
  HARDENED_RETURN_IF_ERROR(dice_cert_check_valid(
      &dice_chain.cert_obj, &dice_chain.subject_pubkey_id,
      &dice_chain.subject_pubkey, &dice_chain.cert_valid));

  return kErrorOk;
}

// Skip the TLV entry if the name matches.
static rom_error_t dice_chain_skip_cert_obj(const char *name,
                                            size_t name_size) {
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj(NULL, 0));
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
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  // Read in a DICE certificate(s) page.
  static_assert(sizeof(dice_chain.data) == FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                "Invalid dice_chain buffer size");
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read_zeros_on_read_error(
      info_page, /*offset=*/0,
      /*word_count=*/FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t),
      dice_chain.data));

  // Resets the flash page status.
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.tail_offset = 0;
  dice_chain.info_page = info_page;
  dice_chain_reset_cert_obj();

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
  HARDENED_RETURN_IF_ERROR(
      perso_tlv_cert_obj_build(name, kPersoObjectTypeX509Cert, cert, cert_size,
                               dice_chain_get_tail_buffer(), &cert_page_left));

  // Move the offset to the new tail.
  HARDENED_RETURN_IF_ERROR(perso_tlv_get_cert_obj(dice_chain_get_tail_buffer(),
                                                  dice_chain_get_tail_size(),
                                                  &dice_chain.cert_obj));
  dice_chain_next_cert_obj();
  return kErrorOk;
}

rom_error_t dice_chain_attestation_silicon(void) {
  // Initialize the entropy complex and KMAC for key manager operations.
  // Note: `OTCRYPTO_OK.value` is equal to `kErrorOk` but we cannot add a static
  // assertion here since its definition is not an integer constant expression.
  HARDENED_RETURN_IF_ERROR((rom_error_t)entropy_complex_init().value);
  HARDENED_RETURN_IF_ERROR(kmac_keymgr_configure());

  // Set keymgr reseed interval. Start with the maximum value to avoid
  // entropy complex contention during the boot process.
  const uint16_t kScKeymgrEntropyReseedInterval = UINT16_MAX;
  sc_keymgr_entropy_reseed_interval_set(kScKeymgrEntropyReseedInterval);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioEntropyReseedIntervalSet);

  // ROM sets the SW binding values for the first key stage (CreatorRootKey) but
  // does not initialize the key manager. Advance key manager state twice to
  // transition to the CreatorRootKey state.
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateInit));

  // Generate UDS keys.
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyUds, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the factory provisioned UDS cert.
  HARDENED_RETURN_IF_ERROR(
      dice_chain_load_flash(&kFlashCtrlInfoPageFactoryCerts));

  // Check if the UDS cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("UDS", /*name_size=*/4));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    // The UDS key ID (and cert itself) should never change unless:
    // 1. there is a hardware issue / the page has been corrupted, or
    // 2. the cert has not yet been provisioned.
    //
    // In both cases, we do nothing, and boot normally, later attestation
    // attempts will fail in a detectable manner.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("Warning: UDS certificate not valid.\r\n");
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();
  }

  // Save UDS key for signing next stage cert.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyUds.keygen_seed_idx, kDiceKeyUds.type,
      *kDiceKeyUds.keymgr_diversifier));
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

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
      kDiceKeyCdi0, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the device generated CDI_0.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));

  // Check if the current CDI_0 cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_0", /*name_size=*/6));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("CDI_0 certificate not valid. Updating it ...\r\n");
    // Update the cert page buffer.
    size_t updated_cert_size = kScratchCertSizeBytes;
    HARDENED_RETURN_IF_ERROR(
        dice_cdi_0_cert_build((hmac_digest_t *)rom_ext_measurement->data,
                              rom_ext_manifest->security_version,
                              &dice_chain.key_ids, &dice_chain.subject_pubkey,
                              dice_chain.scratch_cert, &updated_cert_size));
    HARDENED_RETURN_IF_ERROR(dice_chain_push_cert(
        "CDI_0", dice_chain.scratch_cert, updated_cert_size));
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();

    // Replace UDS with CDI_0 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
        *kDiceKeyCdi0.keymgr_diversifier));
  }
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

  sc_keymgr_sw_binding_unlock_wait();

  return kErrorOk;
}

rom_error_t dice_chain_attestation_owner(
    keymgr_binding_value_t *owner_measurement,
    const manifest_t *owner_manifest) {
  // Generate CDI_1 attestation keys and (potentially) update certificate.
  keymgr_binding_value_t zero_binding_value = {.data = {0}};
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);
  // TODO(cfrantz): setup sealing binding to value specified in owner
  // configuration block.
  HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_advance(
      /*sealing_binding=*/&zero_binding_value,
      /*attest_binding=*/owner_measurement, owner_manifest->max_key_version));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyCdi1, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the device generated CDI_1.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("CDI_0", /*name_size=*/6));

  // Check if the current CDI_0 cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_1", /*name_size=*/6));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("CDI_1 certificate not valid. Updating it ...\r\n");
    // Update the cert page buffer.
    size_t updated_cert_size = kScratchCertSizeBytes;
    // TODO(#19596): add owner configuration block measurement to CDI_1 cert.
    HARDENED_RETURN_IF_ERROR(
        dice_cdi_1_cert_build((hmac_digest_t *)owner_measurement->data,
                              (hmac_digest_t *)zero_binding_value.data,
                              owner_manifest->security_version,
                              &dice_chain.key_ids, &dice_chain.subject_pubkey,
                              dice_chain.scratch_cert, &updated_cert_size));
    HARDENED_RETURN_IF_ERROR(dice_chain_push_cert(
        "CDI_1", dice_chain.scratch_cert, updated_cert_size));
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();

    // Replace CDI_0 with CDI_1 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
        *kDiceKeyCdi1.keymgr_diversifier));
  }
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

  sc_keymgr_sw_binding_unlock_wait();

  return kErrorOk;
}

// Write the DICE certs to flash if they have been updated.
rom_error_t dice_chain_flush_flash(void) {
  if (dice_chain.data_dirty == kHardenedBoolTrue &&
      dice_chain.info_page != NULL) {
    HARDENED_CHECK_EQ(dice_chain.data_dirty, kHardenedBoolTrue);
    HARDENED_RETURN_IF_ERROR(
        flash_ctrl_info_erase(dice_chain.info_page, kFlashCtrlEraseTypePage));
    static_assert(sizeof(dice_chain.data) == FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                  "Invalid dice_chain buffer size");
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        dice_chain.info_page,
        /*offset=*/0,
        /*word_count=*/FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t),
        dice_chain.data));
    dbg_printf("Flushed dice cert page %d\r\n",
               dice_chain.info_page->base_addr);
    dice_chain.data_dirty = kHardenedBoolFalse;
  }
  return kErrorOk;
}

rom_error_t dice_chain_init(void) {
  // Variable initialization.
  memset(&dice_chain, 0, sizeof(dice_chain));
  dice_chain.subject_pubkey = (ecdsa_p256_public_key_t){.x = {0}, .y = {0}};
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.info_page = NULL;
  dice_chain.key_ids = (cert_key_id_pair_t){
      .endorsement = &dice_chain.endorsement_pubkey_id,
      .cert = &dice_chain.subject_pubkey_id,
  };
  dice_chain_reset_cert_obj();

  // Configure DICE certificate flash info page and buffer it into RAM.
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageFactoryCerts,
                          kCertificateInfoPageCfg);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageFactoryCerts);
  return kErrorOk;
}
