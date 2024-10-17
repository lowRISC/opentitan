// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/personalize.h"

#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"
#include "sw/device/silicon_creator/manuf/lib/util.h"

#include "otp_ctrl_regs.h"  // Generated.

static_assert(OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE ==
                  OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE,
              "Detected Root key share size mismatch");
static_assert(OTP_CTRL_PARAM_RMA_TOKEN_SIZE == 16,
              "RMA token is not 128 bits (i.e., one AES block), re-evaluate "
              "padding / AES mode. Additionally, update ujson struct "
              "definition for the wrapped RMA unlock token.");

/**
 * Performs sanity check of buffers holding a masked secret.
 *
 * @param share0 Share 0 buffer.
 * @param share1 Share 1 buffer.
 * @param len Number of 64bit words to sanity check.
 * @return OK_STATUS if share0 ^ share1 is not zero and if both shares don't
 * contain non-zero and non-all-FFs 64bit words.
 */
OT_WARN_UNUSED_RESULT
static status_t shares_check(uint64_t *share0, uint64_t *share1, size_t len) {
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |= share0[i] == share1[i];
    found_error |= share0[i] == UINT64_MAX || share0[i] == 0;
    found_error |= share1[i] == UINT64_MAX || share1[0] == 0;
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

OT_WARN_UNUSED_RESULT
status_t manuf_personalize_flash_asymm_key_seed(
    dif_flash_ctrl_state_t *flash_state, flash_info_field_t field, size_t len) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint32_t seed[kAttestationSeedWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, seed, len,
                             /*fips_check=*/kHardenedBoolTrue));
  TRY(entropy_csrng_uninstantiate());

  // Since all seeds are on stored consecutively on the same flash info page,
  // we only need to set up the permissions on the page, and erase it once.
  uint32_t byte_address = 0;
  if (field.byte_offset == 0) {
    TRY(flash_ctrl_testutils_info_region_scrambled_setup(
        flash_state, field.page, field.bank, field.partition, &byte_address));
    TRY(flash_ctrl_testutils_erase_and_write_page(
        flash_state, byte_address, field.partition, seed,
        kDifFlashCtrlPartitionTypeInfo, kAttestationSeedWords));
  } else {
    dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
    byte_address =
        (field.page * device_info.bytes_per_page) + field.byte_offset;
    TRY(flash_ctrl_testutils_write(flash_state, byte_address, field.partition,
                                   seed, kDifFlashCtrlPartitionTypeInfo,
                                   kAttestationSeedWords));
  }

  uint32_t seed_result[kAttestationSeedWords];
  TRY(flash_ctrl_testutils_read(flash_state, byte_address, field.partition,
                                seed_result, kDifFlashCtrlPartitionTypeInfo,
                                len,
                                /*delay=*/0));
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |=
        seed[i] == 0 || seed[i] == UINT32_MAX || seed[i] != seed_result[i];
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

/**
 * Writes a device-generated keymgr seed to the corresponding flash info page.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the target
 * flash info page.
 *
 * @param flash_state Flash controller instance.
 * @param field Info flash field location information.
 * @param len The number of uint32_t words to program starting at the beginning
 *            of the target flash info field.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t flash_keymgr_secret_seed_write(
    dif_flash_ctrl_state_t *flash_state, flash_info_field_t field, size_t len) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint32_t seed[kFlashInfoKeySeedSizeIn32BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, seed, len,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_uninstantiate());

  uint32_t address = 0;
  TRY(flash_ctrl_testutils_info_region_scrambled_setup(
      flash_state, field.page, field.bank, field.partition, &address));

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash_state, address, field.partition, seed,
      kDifFlashCtrlPartitionTypeInfo, len));

  uint32_t seed_result[kFlashInfoKeySeedSizeIn32BitWords];
  TRY(flash_ctrl_testutils_read(flash_state, address, field.partition,
                                seed_result, kDifFlashCtrlPartitionTypeInfo,
                                len,
                                /*delay=*/0));
  bool found_error = false;
  for (size_t i = 0; i < len; ++i) {
    found_error |=
        seed[i] == 0 || seed[i] == UINT32_MAX || seed[i] != seed_result[i];
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

/**
 * Configures the RMA unlock token and Silicon Creator seed secret shares in the
 * SECRET2 OTP partition.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the SECRET2
 * OTP partition. The data needs to be programmed before the OTP SECRET2
 * partition is locked and when the device is in DEV, PROD, or PROD_END
 * lifecyle state.
 *
 * @param otp_ctrl OTP controller instance.
 * @param rma_unlock_token_hash Hash of the RMA unlock token to store on chip.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_partition_secret2_configure(
    const dif_otp_ctrl_t *otp_ctrl,
    const lc_token_hash_t *rma_unlock_token_hash) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  // Generate RootKey shares.
  uint64_t share0[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share0,
                             kRootKeyShareSizeIn32BitWords,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  uint64_t share1[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share1,
                             kRootKeyShareSizeIn32BitWords,
                             /*fips_check*/ kHardenedBoolTrue));
  TRY(entropy_csrng_uninstantiate());

  TRY(shares_check(share0, share1, kRootKeyShareSizeIn64BitWords));

  // Provision RMA unlock token and RootKey shares into OTP.
  TRY(otp_ctrl_testutils_dai_write64(
      otp_ctrl, kDifOtpCtrlPartitionSecret2, kRmaUnlockTokenOffset,
      rma_unlock_token_hash->hash, kRmaUnlockTokenSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare0, share0,
                                     kRootKeyShareSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare1, share1,
                                     kRootKeyShareSizeIn64BitWords));

  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t manuf_personalize_device_secrets(
    dif_flash_ctrl_state_t *flash_state, const dif_lc_ctrl_t *lc_ctrl,
    const dif_otp_ctrl_t *otp_ctrl,
    const lc_token_hash_t *rma_unlock_token_hash) {
  // Check life cycle in either PROD, PROD_END, or DEV.
  TRY(lc_ctrl_testutils_operational_state_check(lc_ctrl));

  // Skip provisioning of SECRET1 OTP partition if already done.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Check the SECRET1 partition is locked. Flash scrambling seeds must be
  // provisioned before the keymgr seeds can be written to flash info pages, as
  // these pages must be scrambled.
  //
  // Note: for SECRET1 partition to be provisioned, the HW_CFG1 partition
  // must have been provisioned, and the CSRNG SW interface should have been
  // enabled, so no need to check again here.
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  if (!is_locked) {
    return INTERNAL();
  }

  // Re-initialize the entropy complex in continous mode. This also configures
  // the entropy_src health checks in FIPS mode.
  TRY(entropy_complex_init());

  // Provision secret Creator / Owner key seeds in flash.
  // Provision CreatorSeed into target flash info page.
  TRY(flash_keymgr_secret_seed_write(flash_state, kFlashInfoFieldCreatorSeed,
                                     kFlashInfoKeySeedSizeIn32BitWords));
  // Provision preliminary OwnerSeed into target flash info page (with
  // expectation that SiliconOwner will rotate this value during ownership
  // transfer).
  TRY(flash_keymgr_secret_seed_write(flash_state, kFlashInfoFieldOwnerSeed,
                                     kFlashInfoKeySeedSizeIn32BitWords));

  // Provision the OTP SECRET2 partition.
  TRY(otp_partition_secret2_configure(otp_ctrl, rma_unlock_token_hash));

  return OK_STATUS();
}

OT_WARN_UNUSED_RESULT
static status_t otp_secret_write(const dif_otp_ctrl_t *otp_ctrl,
                                 uint32_t offset, size_t len) {
  enum {
    kBufferSize = 4,
  };
  if (len > kBufferSize) {
    return INTERNAL();
  }

  TRY(entropy_csrng_reseed(/*disable_trng_inpu=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  size_t len_in_32bit_words = len * 2;
  uint64_t data[kBufferSize];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)data,
                             len_in_32bit_words,
                             /*fips_check=*/kHardenedBoolTrue));

  bool found_error = false;
  uint64_t prev_val = 0;
  for (size_t i = 0; i < len; ++i) {
    found_error |= data[i] == 0 || data[i] == UINT64_MAX || data[i] == prev_val;
    prev_val = data[i];
  }
  if (found_error) {
    return INTERNAL();
  }

  TRY(otp_ctrl_testutils_dai_write64(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                     offset, data, len));
  return OK_STATUS();
}

status_t manuf_personalize_device_secrets_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret2,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}

status_t manuf_personalize_device_secret1(const dif_lc_ctrl_t *lc_ctrl,
                                          const dif_otp_ctrl_t *otp_ctrl) {
  // Skip provisioning of SECRET1 OTP partition if already done.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Check that the HW_CFG0 OTP partition has been locked (and is activated).
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg0,
                                      &is_locked));
  if (!is_locked) {
    return INTERNAL();
  }

  // Check that the HW_CFG1 OTP partition has been locked (and is activated).
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                      &is_locked));
  if (!is_locked) {
    return INTERNAL();
  }

  // Check that the CSRNG SW application interface is enabled in the HW_CFG1
  // partition, as we cannot provision SECRET1 without access to the CSRNG.
  uint32_t otp_hw_cfg1_settings;
  TRY(otp_ctrl_testutils_dai_read32(otp_ctrl, kDifOtpCtrlPartitionHwCfg1,
                                    kHwCfgEnSramIfetchOffset,
                                    &otp_hw_cfg1_settings));
  uint32_t csrng_sw_app_read =
      bitfield_field32_read(otp_hw_cfg1_settings, kCsrngAppRead);
  if (csrng_sw_app_read != kMultiBitBool8True) {
    return INTERNAL();
  }

  uint32_t dis_rv_dm_late_debug =
      bitfield_field32_read(otp_hw_cfg1_settings, kDisRvDmLateDebug);
  if (dis_rv_dm_late_debug != kMultiBitBool8True) {
    return INTERNAL();
  }

  TRY(entropy_complex_init());
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  TRY(otp_secret_write(otp_ctrl, kSecret1FlashAddrKeySeedOffset,
                       kSecret1FlashAddrKeySeed64BitWords));
  TRY(otp_secret_write(otp_ctrl, kSecret1FlashDataKeySeedOffset,
                       kSecret1FlashDataKeySeed64BitWords));
  TRY(otp_secret_write(otp_ctrl, kSecret1SramDataKeySeedOffset,
                       kSecret1SramDataKeySeed64Bitwords));

  TRY(entropy_csrng_uninstantiate());
  TRY(otp_ctrl_testutils_lock_partition(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t manuf_personalize_device_secret1_check(
    const dif_otp_ctrl_t *otp_ctrl) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp_ctrl, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
