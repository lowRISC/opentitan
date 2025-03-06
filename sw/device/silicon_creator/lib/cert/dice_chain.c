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
#include "sw/device/silicon_creator/lib/base/static_dice_cdi_0.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "flash_ctrl_regs.h"  // Generated.

enum {
  /**
   * The size of the scratch buffer that is large enough for constructing the
   * CDI certs.
   */
  kScratchCertSizeBytes = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
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

cert_key_id_pair_t dice_chain_cdi_0_key_ids = (cert_key_id_pair_t){
    .endorsement = &static_dice_cdi_0.uds_pubkey_id,
    .cert = &static_dice_cdi_0.cdi_0_pubkey_id,
};

// Get the size of the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
OT_NOINLINE
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

  // The cert_size is only 12-bit, which won't cause unsigned overflow.
  cert_size = util_size_to_words(cert_size) * sizeof(uint32_t);
  cert_size = util_round_up_to(cert_size, 3);

  // Jump to the next object.
  dice_chain.tail_offset += cert_size;

  // Post-check for the buffer boundary.
  HARDENED_CHECK_LE(dice_chain.tail_offset, sizeof(dice_chain.data));

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

  RETURN_IF_ERROR(err);

  // Check if this cert is what we are looking for.
  if (name == NULL || memcmp(dice_chain.cert_obj.name, name, name_size) != 0) {
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
  static_assert(sizeof(dice_chain.data) == FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                "Invalid dice_chain buffer size");
  RETURN_IF_ERROR(flash_ctrl_info_read_zeros_on_read_error(
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
  RETURN_IF_ERROR(
      perso_tlv_cert_obj_build(name, kPersoObjectTypeX509Cert, cert, cert_size,
                               dice_chain_get_tail_buffer(), &cert_page_left));

  // Move the offset to the new tail.
  RETURN_IF_ERROR(perso_tlv_get_cert_obj(dice_chain_get_tail_buffer(),
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

  // Switch page for the device generated CDI_0.
  RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));

  // Check if the current CDI_0 cert is valid.
  RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_0", /*name_size=*/6));
  if (dice_chain.cert_valid == kHardenedBoolFalse) {
    // Update the cert page buffer.
    static_dice_cdi_0.cert_size = sizeof(static_dice_cdi_0.cert_data);
    HARDENED_RETURN_IF_ERROR(dice_cdi_0_cert_build(
        (hmac_digest_t *)rom_ext_measurement->data,
        rom_ext_manifest->security_version, &dice_chain_cdi_0_key_ids,
        &static_dice_cdi_0.cdi_0_pubkey, static_dice_cdi_0.cert_data,
        &static_dice_cdi_0.cert_size));
  } else {
    // Replace UDS with CDI_0 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
        *kDiceKeyCdi0.keymgr_diversifier));
  }

  sc_keymgr_sw_binding_unlock_wait();

  return kErrorOk;
}

// Compare the UDS identity in the static critical section to the UDS cert
// cached in the flash.
static rom_error_t dice_chain_attestation_check_uds(void) {
  // Switch page for the factory provisioned UDS cert.
  RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageFactoryCerts));

  // Check if the UDS cert is valid.
  dice_chain.endorsement_pubkey_id = static_dice_cdi_0.uds_pubkey_id;
  dice_chain.subject_pubkey_id = static_dice_cdi_0.uds_pubkey_id;
  dice_chain.subject_pubkey = static_dice_cdi_0.uds_pubkey;
  RETURN_IF_ERROR(dice_chain_load_cert_obj("UDS", /*name_size=*/4));
  if (dice_chain.cert_valid == kHardenedBoolFalse) {
    // The UDS key ID (and cert itself) should never change unless:
    // 1. there is a hardware issue / the page has been corrupted, or
    // 2. the cert has not yet been provisioned.
    //
    // In both cases, we do nothing, and boot normally, later attestation
    // attempts will fail in a detectable manner.

    // CAUTION: This error message should match the one in
    //   //sw/host/provisioning/ft_lib/src/lib.rs
    dbg_puts("error: UDS certificate not valid\r\n");
  }

  return kErrorOk;
}

// Compare the CDI_0 identity in the static critical section to the CDI_0 cert
// cached in the flash, and refresh the cache if invalid.
static rom_error_t dice_chain_attestation_check_cdi_0(void) {
  // Switch page for the device CDI chain.
  RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));

  // Refresh cdi 0 if invalid
  dice_chain.endorsement_pubkey_id = static_dice_cdi_0.cdi_0_pubkey_id;
  dice_chain.subject_pubkey_id = static_dice_cdi_0.cdi_0_pubkey_id;
  dice_chain.subject_pubkey = static_dice_cdi_0.cdi_0_pubkey;
  RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_0", /*name_size=*/6));
  if (dice_chain.cert_valid == kHardenedBoolFalse) {
    dbg_puts("warning: CDI_0 certificate not valid; updating\r\n");
    // Update the cert page buffer.
    RETURN_IF_ERROR(dice_chain_push_cert("CDI_0", static_dice_cdi_0.cert_data,
                                         static_dice_cdi_0.cert_size));
  } else {
    // Cert is valid, move to the next one.
    dice_chain_next_cert_obj();
  }

  return kErrorOk;
}

rom_error_t dice_chain_attestation_owner(
    const manifest_t *owner_manifest, keymgr_binding_value_t *bl0_measurement,
    hmac_digest_t *owner_measurement, keymgr_binding_value_t *sealing_binding,
    owner_app_domain_t key_domain) {
  // Handles the certificates from the immutable rom_ext first.
  RETURN_IF_ERROR(dice_chain_attestation_check_uds());
  RETURN_IF_ERROR(dice_chain_attestation_check_cdi_0());

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
      kDiceKeyCdi1, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Check if the current CDI_1 cert is valid.
  RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_1", /*name_size=*/6));
  if (dice_chain.cert_valid == kHardenedBoolFalse) {
    dbg_puts("CDI_1 certificate not valid. Updating it ...\r\n");
    // Update the cert page buffer.
    size_t updated_cert_size = kScratchCertSizeBytes;
    // TODO(#19596): add owner configuration block measurement to CDI_1 cert.
    HARDENED_RETURN_IF_ERROR(dice_cdi_1_cert_build(
        (hmac_digest_t *)bl0_measurement, owner_measurement,
        owner_manifest->security_version, key_domain, &dice_chain.key_ids,
        &dice_chain.subject_pubkey, dice_chain.scratch_cert,
        &updated_cert_size));
    RETURN_IF_ERROR(dice_chain_push_cert("CDI_1", dice_chain.scratch_cert,
                                         updated_cert_size));
  } else {
    // Cert is valid, move to the next one.
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
    RETURN_IF_ERROR(
        flash_ctrl_info_erase(dice_chain.info_page, kFlashCtrlEraseTypePage));
    static_assert(sizeof(dice_chain.data) == FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                  "Invalid dice_chain buffer size");
    RETURN_IF_ERROR(flash_ctrl_info_write(
        dice_chain.info_page,
        /*offset=*/0,
        /*word_count=*/FLASH_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t),
        dice_chain.data));
    dice_chain.data_dirty = kHardenedBoolFalse;
  }
  return kErrorOk;
}

rom_error_t dice_chain_init(void) {
  // Variable initialization.
  memset(&dice_chain, 0, sizeof(dice_chain));
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.key_ids = (cert_key_id_pair_t){
      .endorsement = &dice_chain.endorsement_pubkey_id,
      .cert = &dice_chain.subject_pubkey_id,
  };
  dice_chain_reset_cert_obj();

  // Configure DICE certificate flash info page and buffer it into RAM.
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageFactoryCerts,
                          kCertificateInfoPageCfg);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageFactoryCerts);
  return kErrorOk;
}
