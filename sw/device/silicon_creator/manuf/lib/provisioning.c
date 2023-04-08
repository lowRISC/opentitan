// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/manuf/lib/provisioning.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"

#include "otp_ctrl_regs.h"

enum {
  kRootKeyShareSizeInBytes = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE,
  kRootKeyShareSizeIn32BitWords = kRootKeyShareSizeInBytes / sizeof(uint32_t),
  kRootKeyShareSizeIn64BitWords = kRootKeyShareSizeInBytes / sizeof(uint64_t),
  kRootKeyOffsetShare0 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,
  kRootKeyOffsetShare1 = OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET -
                         OTP_CTRL_PARAM_SECRET2_OFFSET,

  kCreatorSeedSizeInBytes = 32,
  kCreatorSeedSizeInWords = kCreatorSeedSizeInBytes / sizeof(uint32_t),

  /** Flash Secret partition ID. */
  kFlashInfoPartitionId = 0,

  /** Secret partition flash bank ID. */
  kFlashInfoBankId = 0,

  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  kOtpDefaultBlankValue = 0,
};
static_assert(OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE ==
                  OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE,
              "Detected Root key share size mismatch");

/**
 * Checks the device life cycle state to determine if it is ok to proceed with
 * provisioning.
 *
 * @param lc_ctrl Life cycle controller instance.
 * @return OK_STATUS if the device is in PROD, PROD_END or DEV state; otherwise
 * FAILED_PRECONDITION.
 */
OT_WARN_UNUSED_RESULT
static status_t lc_ctrl_state_check(const dif_lc_ctrl_t *lc_ctrl) {
  // TODO: Switch to lc_ctrl_testutils.
  dif_lc_ctrl_state_t state;
  TRY(dif_lc_ctrl_get_state(lc_ctrl, &state));
  if (state == kDifLcCtrlStateProd || state == kDifLcCtrlStateProdEnd ||
      state == kDifLcCtrlStateDev) {
    return OK_STATUS();
  }
  return FAILED_PRECONDITION();
}

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

/**
 * Checks if the SECRET2 OTP partition is in locked state.
 *
 * @param otp otp_ctrl instance.
 * @param[out] is_locked Set to true if the SECRET2 partition is locked.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_partition_secret2_is_locked(const dif_otp_ctrl_t *otp,
                                                bool *is_locked) {
  TRY(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionSecret2,
                                      is_locked));
  return OK_STATUS();
}

/**
 * Configures the Silicon Creator Secret Seed in flash.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the Silicon
 * Creator Seed flash info page. This value needs to be configured before the
 * OTP SECRET2 partition is locked and when the device is in PROD, PROD_END, DEV
 * or RMA lifecyle state.
 *
 * @param flash_state Flash controller instance.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t flash_ctrl_creator_secret_write(
    dif_flash_ctrl_state_t *flash_state) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint32_t creator_seed[kCreatorSeedSizeInWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, creator_seed,
                             kCreatorSeedSizeInWords));
  TRY(entropy_csrng_uninstantiate());

  uint32_t address = 0;
  TRY(flash_ctrl_testutils_info_region_scrambled_setup(
      flash_state, kFlashInfoPageIdCreatorSecret, kFlashInfoBankId,
      kFlashInfoPartitionId, &address));

  TRY(flash_ctrl_testutils_erase_and_write_page(
      flash_state, address, kFlashInfoPartitionId, creator_seed,
      kDifFlashCtrlPartitionTypeInfo, kCreatorSeedSizeInWords));

  uint32_t creator_seed_result[kCreatorSeedSizeInWords];
  TRY(flash_ctrl_testutils_read(
      flash_state, address, kFlashInfoPartitionId, creator_seed_result,
      kDifFlashCtrlPartitionTypeInfo, kCreatorSeedSizeInWords, /*delay=*/0));
  bool found_error = false;
  for (size_t i = 0; i < kCreatorSeedSizeInWords; ++i) {
    found_error |= creator_seed[i] == 0 || creator_seed[i] == UINT32_MAX ||
                   creator_seed[i] != creator_seed_result[i];
  }
  return found_error ? INTERNAL() : OK_STATUS();
}

/**
 * Configures the Silicon Creator seed secret shares in the SECRET2 OTP
 * partition.
 *
 * Entropy is extracted from the CSRNG instance and programmed into the SECRET2
 * OTP partition. The data needs to be programmed before the OTP SECRET2
 * partition is locked and when the device is in PROD, PROD_END, DEV or RMA
 * lifecyle state.
 *
 * @param otp OTP controller instance.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_partition_secret2_configure(const dif_otp_ctrl_t *otp) {
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  uint64_t share0[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share0,
                             kRootKeyShareSizeIn32BitWords));

  TRY(entropy_csrng_reseed(/*disable_trng_inpu=*/kHardenedBoolFalse,
                           /*seed_material=*/NULL));

  uint64_t share1[kRootKeyShareSizeIn64BitWords];
  TRY(entropy_csrng_generate(/*seed_material=*/NULL, (uint32_t *)share1,
                             kRootKeyShareSizeIn32BitWords));
  TRY(entropy_csrng_uninstantiate());

  TRY(shares_check(share0, share1, kRootKeyShareSizeIn64BitWords));

  TRY(otp_ctrl_testutils_dai_write64(otp, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare0, share0,
                                     kRootKeyShareSizeIn64BitWords));
  TRY(otp_ctrl_testutils_dai_write64(otp, kDifOtpCtrlPartitionSecret2,
                                     kRootKeyOffsetShare1, share1,
                                     kRootKeyShareSizeIn64BitWords));
  TRY(shares_check(share0, share1, kRootKeyShareSizeIn64BitWords));

  TRY(otp_ctrl_testutils_lock_partition(otp, kDifOtpCtrlPartitionSecret2,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t provisioning_device_secrets_start(dif_flash_ctrl_state_t *flash_state,
                                           const dif_lc_ctrl_t *lc_ctrl,
                                           const dif_otp_ctrl_t *otp) {
  // Check life cycle in either PROD or DEV.
  TRY(lc_ctrl_state_check(lc_ctrl));

  // Skip if SECRET2 partition is locked. We won't be able to configure the
  // secret info flash page nor the OTP secrets if the OTP SECRET2 partition is
  // locked.
  bool is_locked;
  TRY(otp_partition_secret2_is_locked(otp, &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Re-initialize the entropy complex in continous mode. This also configures
  // the entropy_src health checks in FIPS mode.
  TRY(entropy_complex_init());
  TRY(flash_ctrl_creator_secret_write(flash_state));
  TRY(otp_partition_secret2_configure(otp));
  return OK_STATUS();
}

status_t provisioning_device_secrets_end(const dif_otp_ctrl_t *otp) {
  bool is_locked;
  TRY(otp_partition_secret2_is_locked(otp, &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
