// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/silicon_creator/manuf/lib/individualize.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"

#include "otp_ctrl_regs.h"

enum {
  /**
   * Secret1 Parition OTP fields.
   */
  kSecret1FlashAddrKeySeedOffset =
      OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1FlashAddrKeySeed64BitWords =
      OTP_CTRL_PARAM_FLASH_ADDR_KEY_SEED_SIZE / sizeof(uint64_t),

  kSecret1FlashDataKeySeedOffset =
      OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1FlashDataKeySeed64BitWords =
      OTP_CTRL_PARAM_FLASH_DATA_KEY_SEED_SIZE / sizeof(uint64_t),

  kSecret1SramDataKeySeedOffset =
      OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_OFFSET - OTP_CTRL_PARAM_SECRET1_OFFSET,
  kSecret1SramDataKeySeed64Bitwords =
      OTP_CTRL_PARAM_SRAM_DATA_KEY_SEED_SIZE / sizeof(uint64_t),

  /**
   * DeviceId offset and length.
   * The offset is relative to the start of the HW_CFG OTP partition.
   */
  kHwCfgDeviceIdOffset =
      OTP_CTRL_PARAM_DEVICE_ID_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,
  kHwCfgDeviceIdWordCount = OTP_CTRL_PARAM_DEVICE_ID_SIZE / sizeof(uint32_t),

  /**
   * ManufState offset and length.
   * The offset is relative to the start of the HW_CFG OTP parition.
   */
  kHwCfgManufStateOffset =
      OTP_CTRL_PARAM_MANUF_STATE_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,
  kHwCfgManufStateWordCount =
      OTP_CTRL_PARAM_MANUF_STATE_SIZE / sizeof(uint32_t),

  /**
   * Offset to the EN_SRAM_IFETCH OTP bits relative to the start of the HW_CFG
   * partition.
   */
  kHwCfgEnSramIfetchOffset =
      OTP_CTRL_PARAM_EN_SRAM_IFETCH_OFFSET - OTP_CTRL_PARAM_HW_CFG_OFFSET,

  /**
   * DeviceID info flash location. This assumes the device ID is written to
   * flash during CP testing. This test case is provided as a reference
   * implementation. Manufactures may modify the way DeviceId generated and
   * written into OTP.
   */
  kFlashInfoDeviceIdPartitionId = 0,
  kFlashInfoDeviceIdBankId = 0,
  kFlashInfoDeviceIdPageId = 0,
  kFlashInfoDeviceIdByteAddress = 0,
  kFlashInfoDeviceIdWordCount = kHwCfgDeviceIdWordCount,

  /**
   * ManufState info flash location. This assumes the manuf state is written to
   * flash before invoking this test library.
   */
  kFlashInfoManufStatePartitionId = 0,
  kFlashInfoManufStateBankId = 0,
  kFlashInfoManufStatePageId = 0,
  kFlashInfoManufStateByteAddress = kHwCfgDeviceIdWordCount * sizeof(uint32_t),
  kFlashInfoManufStateWordCount = kHwCfgManufStateWordCount,
};

typedef struct hw_cfg_settings {
  /**
   * Enable / disable execute from SRAM CSR switch.
   */
  multi_bit_bool_t en_sram_ifetch;
  /**
   * This input efuse is used to enable access to the NIST internal state per
   * instance.
   */
  multi_bit_bool_t en_csrng_sw_app_read;
  /**
   * This input efuse is used to enable access to the ENTROPY_DATA register
   * directly.
   */
  multi_bit_bool_t en_entropy_src_fw_read;
  /**
   * This input efuse is used to enable access to the firmware override FIFO and
   * other related functions.
   */
  multi_bit_bool_t en_entropy_src_fw_over;
} hw_cfg_settings_t;

// Changing any of the following values may result in unexpected device
// behavior.
//
// - en_sram_ifetch: required to enable SRAM code execution during
//   manufacturing.
// - en_csrng_sw_app_read: required to be able to extract output from CSRNG.
// - en_entropy_src_fw_read and en_entropy_src_fw_over: Required to implement
//   entropy_src conditioner KAT.
const hw_cfg_settings_t kHwCfgSettings = {
    .en_sram_ifetch = kMultiBitBool8True,
    .en_csrng_sw_app_read = kMultiBitBool8True,
    .en_entropy_src_fw_read = kMultiBitBool8True,
    .en_entropy_src_fw_over = kMultiBitBool8True,
};

/**
 * Configures digital logic settings in the HW_CFG partition.
 *
 * @param otp OTP controller instance.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t hw_cfg_enable_knobs_set(const dif_otp_ctrl_t *otp) {
#define HW_CFG_EN_OFFSET(m, i) ((bitfield_field32_t){.mask = m, .index = i})
  static const bitfield_field32_t kSramFetch = HW_CFG_EN_OFFSET(0xff, 0);
  static const bitfield_field32_t kCsrngAppRead = HW_CFG_EN_OFFSET(0xff, 8);
  static const bitfield_field32_t kEntropySrcFwRd = HW_CFG_EN_OFFSET(0xff, 16);
  static const bitfield_field32_t kEntropySrcFwOvr = HW_CFG_EN_OFFSET(0xff, 24);
#undef HW_CFG_EN_OFFSET

  uint32_t val =
      bitfield_field32_write(0, kSramFetch, kHwCfgSettings.en_sram_ifetch);
  val = bitfield_field32_write(val, kCsrngAppRead,
                               kHwCfgSettings.en_csrng_sw_app_read);
  val = bitfield_field32_write(val, kEntropySrcFwRd,
                               kHwCfgSettings.en_entropy_src_fw_read);
  val = bitfield_field32_write(val, kEntropySrcFwOvr,
                               kHwCfgSettings.en_entropy_src_fw_over);

  TRY(otp_ctrl_testutils_dai_write32(otp, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgEnSramIfetchOffset, &val,
                                     /*len=*/1));
  return OK_STATUS();
}

/**
 * Reads info flash page.
 *
 * Note: This function assumes that the data stored in info flash is unscrambled
 * and ECC enabled.
 *
 * @param flash_state Flash controller instance.
 * @param relative_address Byte address relative to the start of the page.
 * @param partition_id Info flash partition Id.
 * @param page_id Page Id.
 * @param[out] data_out Output buffer.
 * @param word_count Number of words to read from flash and write to `data_out`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t flash_info_read(dif_flash_ctrl_state_t *flash_state,
                                uint32_t relative_address,
                                uint32_t partition_id, uint32_t page_id,
                                uint32_t *data_out, uint32_t word_count) {
  uint32_t byte_address = 0;

  // Enable read access and calculate the `byte_address` with respect to the
  // flash bank.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_state, page_id, /*bank=*/0, partition_id,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4False,
          .rd_en = kMultiBitBool4True,
          .scramble_en = kMultiBitBool4False},
      &byte_address));

  TRY(flash_ctrl_testutils_read(flash_state, byte_address, partition_id,
                                data_out, kDifFlashCtrlPartitionTypeInfo,
                                word_count,
                                /*delay=*/0));

  // Disable all access after done.
  TRY(flash_ctrl_testutils_info_region_setup_properties(
      flash_state, page_id, /*bank=*/0, partition_id,
      (dif_flash_ctrl_region_properties_t){
          .ecc_en = kMultiBitBool4True,
          .high_endurance_en = kMultiBitBool4False,
          .erase_en = kMultiBitBool4False,
          .prog_en = kMultiBitBool4False,
          .rd_en = kMultiBitBool4False,
          .scramble_en = kMultiBitBool4False},
      &byte_address));

  return OK_STATUS();
}

status_t individualize_dev_hw_cfg_start(dif_flash_ctrl_state_t *flash_state,
                                        const dif_lc_ctrl_t *lc_ctrl,
                                        const dif_otp_ctrl_t *otp) {
  TRY(lc_ctrl_testutils_operational_state_check(lc_ctrl));

  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionHwCfg,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  // Configure byte-sized hardware enable knobs.
  TRY(hw_cfg_enable_knobs_set(otp));

  // Configure DeviceID
  uint32_t device_id[kFlashInfoDeviceIdWordCount];
  TRY(flash_info_read(flash_state, kFlashInfoDeviceIdByteAddress,
                      kFlashInfoDeviceIdPartitionId, kFlashInfoDeviceIdPageId,
                      device_id, kFlashInfoDeviceIdWordCount));
  TRY(otp_ctrl_testutils_dai_write32(otp, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgDeviceIdOffset, device_id,
                                     kHwCfgDeviceIdWordCount));

  // Configure ManufState
  uint32_t manuf_state[kFlashInfoManufStateWordCount];
  TRY(flash_info_read(flash_state, kFlashInfoManufStateByteAddress,
                      kFlashInfoManufStatePartitionId,
                      kFlashInfoManufStatePageId, manuf_state,
                      kFlashInfoManufStateWordCount));
  TRY(otp_ctrl_testutils_dai_write32(otp, kDifOtpCtrlPartitionHwCfg,
                                     kHwCfgManufStateOffset, manuf_state,
                                     kHwCfgManufStateWordCount));

  TRY(otp_ctrl_testutils_lock_partition(otp, kDifOtpCtrlPartitionHwCfg,
                                        /*digest=*/0));
  return OK_STATUS();
}

status_t individualize_dev_hw_cfg_end(const dif_otp_ctrl_t *otp) {
  // TODO: Add DeviceId by comparing OTP flash value against the value reported
  // by lc_ctrl. Consider erasing the data from the flash info pages.
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionHwCfg,
                                      &is_locked));
  uint64_t digest;
  TRY(dif_otp_ctrl_get_digest(otp, kDifOtpCtrlPartitionHwCfg, &digest));

  return is_locked ? OK_STATUS() : INTERNAL();
}

OT_WARN_UNUSED_RESULT
status_t otp_secret_write(const dif_otp_ctrl_t *otp, uint32_t offset,
                          size_t len) {
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
                             len_in_32bit_words));

  bool found_error = false;
  uint64_t prev_val = 0;
  for (size_t i = 0; i < len; ++i) {
    found_error |= data[i] == 0 || data[i] == UINT64_MAX || data[i] == prev_val;
    prev_val = data[i];
  }
  if (found_error) {
    return INTERNAL();
  }

  TRY(otp_ctrl_testutils_dai_write64(otp, kDifOtpCtrlPartitionSecret1, offset,
                                     data, len));
  return OK_STATUS();
}

status_t individualize_dev_secret1_start(const dif_lc_ctrl_t *lc_ctrl,
                                         const dif_otp_ctrl_t *otp) {
  // Check life cycle in either PROD or DEV.
  TRY(lc_ctrl_testutils_operational_state_check(lc_ctrl));

  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  if (is_locked) {
    return OK_STATUS();
  }

  TRY(entropy_complex_init());
  TRY(entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                /*seed_material=*/NULL));

  TRY(otp_secret_write(otp, kSecret1FlashAddrKeySeedOffset,
                       kSecret1FlashAddrKeySeed64BitWords));
  TRY(otp_secret_write(otp, kSecret1FlashDataKeySeedOffset,
                       kSecret1FlashDataKeySeed64BitWords));
  TRY(otp_secret_write(otp, kSecret1SramDataKeySeedOffset,
                       kSecret1SramDataKeySeed64Bitwords));

  TRY(entropy_csrng_uninstantiate());
  TRY(otp_ctrl_testutils_lock_partition(otp, kDifOtpCtrlPartitionSecret1,
                                        /*digest=*/0));

  return OK_STATUS();
}

status_t individualize_dev_secret1_end(const dif_otp_ctrl_t *otp) {
  bool is_locked;
  TRY(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionSecret1,
                                      &is_locked));
  return is_locked ? OK_STATUS() : INTERNAL();
}
