// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/flash_ctrl_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/check.h"

#include "flash_ctrl_regs.h"  // Generated.

void flash_ctrl_testutils_wait_for_init(dif_flash_ctrl_state_t *flash_state) {
  dif_flash_ctrl_status_t status;
  do {
    CHECK_DIF_OK(dif_flash_ctrl_get_status(flash_state, &status));
  } while (status.controller_init_wip);
}

bool flash_ctrl_testutils_wait_transaction_end(
    dif_flash_ctrl_state_t *flash_state) {
  dif_flash_ctrl_output_t output;
  while (true) {
    dif_result_t dif_result = dif_flash_ctrl_end(flash_state, &output);
    CHECK(dif_result != kDifBadArg);
    CHECK(dif_result != kDifError);
    if (dif_result == kDifOk) {
      break;
    }
  }
  if (output.operation_error) {
    dif_flash_ctrl_error_codes_t codes = output.error_code.codes;
    uint32_t error_reg = 0;
    error_reg = bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_MP_ERR_BIT,
                                     codes.memory_properties_error);
    error_reg = bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_RD_ERR_BIT,
                                     codes.read_error);
    error_reg =
        bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT,
                             codes.prog_window_error);
    error_reg =
        bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT,
                             codes.prog_type_error);
    error_reg =
        bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_FLASH_MACRO_ERR_BIT,
                             codes.flash_phy_error);
    error_reg =
        bitfield_bit32_write(error_reg, FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT,
                             codes.shadow_register_error);
    LOG_INFO("Transaction end error_codes = %08x", error_reg);
  }
  CHECK_DIF_OK(
      dif_flash_ctrl_clear_error_codes(flash_state, output.error_code.codes));
  return output.operation_error;
}

uint32_t flash_ctrl_testutils_data_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size,
    dif_flash_ctrl_region_properties_t region_properties) {
  dif_flash_ctrl_data_region_properties_t data_region_properties = {
      .base = base_page_index,
      .properties = region_properties,
      .size = region_size};

  CHECK_DIF_OK(dif_flash_ctrl_set_data_region_properties(
      flash_state, data_region, data_region_properties));
  CHECK_DIF_OK(dif_flash_ctrl_set_data_region_enablement(
      flash_state, data_region, kDifToggleEnabled));

  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  return (base_page_index * device_info.bytes_per_page);
}

uint32_t flash_ctrl_testutils_data_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False,
      .erase_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False};
  return flash_ctrl_testutils_data_region_setup_properties(
      flash_state, base_page_index, data_region, region_size,
      region_properties);
}

uint32_t flash_ctrl_testutils_data_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False,
      .erase_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True};
  return flash_ctrl_testutils_data_region_setup_properties(
      flash_state, base_page_index, data_region, region_size,
      region_properties);
}

uint32_t flash_ctrl_testutils_info_region_setup_properties(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id,
    dif_flash_ctrl_region_properties_t region_properties) {
  dif_flash_ctrl_info_region_t info_region = {
      .bank = bank, .page = page_id, .partition_id = partition_id};

  CHECK_DIF_OK(dif_flash_ctrl_set_info_region_properties(
      flash_state, info_region, region_properties));
  CHECK_DIF_OK(dif_flash_ctrl_set_info_region_enablement(
      flash_state, info_region, kDifToggleEnabled));

  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  return (page_id * device_info.bytes_per_page);
}

uint32_t flash_ctrl_testutils_info_region_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False,
      .erase_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False};
  return flash_ctrl_testutils_info_region_setup_properties(
      flash_state, page_id, bank, partition_id, region_properties);
}

uint32_t flash_ctrl_testutils_info_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .high_endurance_en = kMultiBitBool4False,
      .erase_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True};
  return flash_ctrl_testutils_info_region_setup_properties(
      flash_state, page_id, bank, partition_id, region_properties);
}

bool flash_ctrl_testutils_erase_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, dif_flash_ctrl_partition_type_t partition_type) {
  dif_flash_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                              .op = kDifFlashCtrlOpPageErase,
                                              .partition_type = partition_type,
                                              .partition_id = partition_id,
                                              .word_count = 0x0};
  CHECK_DIF_OK(dif_flash_ctrl_start(flash_state, transaction));
  return flash_ctrl_testutils_wait_transaction_end(flash_state);
}

bool flash_ctrl_testutils_write(dif_flash_ctrl_state_t *flash_state,
                                uint32_t byte_address, uint32_t partition_id,
                                const uint32_t *data,
                                dif_flash_ctrl_partition_type_t partition_type,
                                uint32_t word_count) {
  // Cannot program partial flash words.
  if (byte_address & (FLASH_CTRL_PARAM_BYTES_PER_WORD - 1)) {
    return false;
  }
  dif_flash_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                              .op = kDifFlashCtrlOpProgram,
                                              .partition_type = partition_type,
                                              .partition_id = partition_id,
                                              .word_count = 0x0};
  static_assert(FLASH_CTRL_PARAM_BYTES_PER_WORD >= sizeof(uint32_t),
                "flash_ctrl_testutils_write() assumes the flash word width is"
                "greater than or equal to the bus word width.");
  uint32_t words_written = 0;
  uint32_t word_address = byte_address / sizeof(uint32_t);
  const uint32_t prog_window_size =
      (uint32_t)FLASH_CTRL_PARAM_REG_BUS_PGM_RES_BYTES / sizeof(uint32_t);
  const uint32_t prog_window_mask = ~(prog_window_size - 1);
  bool retval = false;
  while (words_written < word_count) {
    // Writes must not cross programming resolution window boundaries, which
    // occur at every prog_window_size words.
    uint32_t window_limit =
        ((word_address + prog_window_size) & prog_window_mask) - word_address;
    uint32_t words_remaining = word_count - words_written;
    uint32_t words_to_write =
        (words_remaining < window_limit) ? words_remaining : window_limit;
    transaction.byte_address = word_address * sizeof(uint32_t);
    transaction.word_count = words_to_write;
    CHECK_DIF_OK(dif_flash_ctrl_start(flash_state, transaction));
    CHECK_DIF_OK(dif_flash_ctrl_prog_fifo_push(flash_state, words_to_write,
                                               data + words_written));
    retval |= flash_ctrl_testutils_wait_transaction_end(flash_state);
    word_address += words_to_write;
    words_written += words_to_write;
  }

  return retval;
}

bool flash_ctrl_testutils_erase_and_write_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, const uint32_t *data,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count) {
  bool retval = flash_ctrl_testutils_erase_page(flash_state, byte_address,
                                                partition_id, partition_type);
  retval |= flash_ctrl_testutils_write(flash_state, byte_address, partition_id,
                                       data, partition_type, word_count);
  return retval;
}

bool flash_ctrl_testutils_read(dif_flash_ctrl_state_t *flash_state,
                               uint32_t byte_address, uint32_t partition_id,
                               uint32_t *data_out,
                               dif_flash_ctrl_partition_type_t partition_type,
                               uint32_t word_count, uint32_t delay) {
  dif_flash_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                              .op = kDifFlashCtrlOpRead,
                                              .partition_type = partition_type,
                                              .partition_id = partition_id,
                                              .word_count = word_count};

  // Read Page.
  CHECK_DIF_OK(dif_flash_ctrl_start(flash_state, transaction));
  // Optional delay to allow for read fifo fill testing.
  busy_spin_micros(delay);
  CHECK_DIF_OK(dif_flash_ctrl_read_fifo_pop(flash_state, word_count, data_out));
  return flash_ctrl_testutils_wait_transaction_end(flash_state);
}

void flash_ctrl_testutils_default_region_access(
    dif_flash_ctrl_state_t *flash_state, bool rd_en, bool prog_en,
    bool erase_en, bool scramble_en, bool ecc_en, bool high_endurance_en) {
  dif_flash_ctrl_region_properties_t default_properties = {
      .rd_en = rd_en ? kMultiBitBool4True : kMultiBitBool4False,
      .prog_en = prog_en ? kMultiBitBool4True : kMultiBitBool4False,
      .erase_en = erase_en ? kMultiBitBool4True : kMultiBitBool4False,
      .scramble_en = scramble_en ? kMultiBitBool4True : kMultiBitBool4False,
      .ecc_en = ecc_en ? kMultiBitBool4True : kMultiBitBool4False,
      .high_endurance_en =
          high_endurance_en ? kMultiBitBool4True : kMultiBitBool4False};

  CHECK_DIF_OK(dif_flash_ctrl_set_default_region_properties(
      flash_state, default_properties));
}

bool flash_ctrl_testutils_bank_erase(dif_flash_ctrl_state_t *flash_state,
                                     uint32_t bank, bool data_only) {
  dif_toggle_t bank_erase_enabled;
  CHECK_DIF_OK(dif_flash_ctrl_get_bank_erase_enablement(flash_state, bank,
                                                        &bank_erase_enabled));

  if (bank_erase_enabled == kDifToggleDisabled) {
    CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(flash_state, bank,
                                                          kDifToggleEnabled));
  }

  dif_flash_ctrl_device_info_t flash_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      bank * flash_info.bytes_per_page * flash_info.data_pages;
  dif_flash_ctrl_partition_type_t partition_type =
      data_only ? kDifFlashCtrlPartitionTypeData
                : kDifFlashCtrlPartitionTypeInfo;
  dif_flash_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                              .op = kDifFlashCtrlOpBankErase,
                                              .partition_type = partition_type,
                                              .partition_id = 0,
                                              .word_count = 0x0};
  CHECK_DIF_OK(dif_flash_ctrl_start(flash_state, transaction));
  bool retval = flash_ctrl_testutils_wait_transaction_end(flash_state);

  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(flash_state, bank,
                                                        bank_erase_enabled));

  return retval;
}
