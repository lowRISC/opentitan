// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/flash_ctrl_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/check.h"

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
    LOG_INFO("Transaction end error_codes = %0x", output.error_code.codes);
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
      .ecc_en = true,
      .high_endurance_en = false,
      .erase_en = true,
      .prog_en = true,
      .rd_en = true,
      .scramble_en = false};
  return flash_ctrl_testutils_data_region_setup_properties(
      flash_state, base_page_index, data_region, region_size,
      region_properties);
}

uint32_t flash_ctrl_testutils_data_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = true,
      .high_endurance_en = false,
      .erase_en = true,
      .prog_en = true,
      .rd_en = true,
      .scramble_en = true};
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
      .ecc_en = true,
      .high_endurance_en = false,
      .erase_en = true,
      .prog_en = true,
      .rd_en = true,
      .scramble_en = false};
  return flash_ctrl_testutils_info_region_setup_properties(
      flash_state, page_id, bank, partition_id, region_properties);
}

uint32_t flash_ctrl_testutils_info_region_scrambled_setup(
    dif_flash_ctrl_state_t *flash_state, uint32_t page_id, uint32_t bank,
    uint32_t partition_id) {
  dif_flash_ctrl_region_properties_t region_properties = {
      .ecc_en = true,
      .high_endurance_en = false,
      .erase_en = true,
      .prog_en = true,
      .rd_en = true,
      .scramble_en = true};
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

bool flash_ctrl_testutils_write_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, const uint32_t *data,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count) {
  dif_flash_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                              .op = kDifFlashCtrlOpProgram,
                                              .partition_type = partition_type,
                                              .partition_id = partition_id,
                                              .word_count = 0x0};
  uint32_t words_written = 0;
  bool retval = false;
  // The flash will accept a maximum of MAX_BEATS_PER_BURST per write
  // before the transaction must be ended and a new one started.
  while (words_written < word_count) {
    uint32_t words_to_write =
        ((word_count - words_written) < MAX_BEATS_PER_BURST)
            ? (word_count - words_written)
            : MAX_BEATS_PER_BURST;
    transaction.word_count = words_to_write;
    transaction.byte_address =
        byte_address + (sizeof(uint32_t) * words_written);
    CHECK_DIF_OK(dif_flash_ctrl_start(flash_state, transaction));
    CHECK_DIF_OK(dif_flash_ctrl_prog_fifo_push(flash_state, words_to_write,
                                               data + words_written));
    retval |= flash_ctrl_testutils_wait_transaction_end(flash_state);
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
  retval |=
      flash_ctrl_testutils_write_page(flash_state, byte_address, partition_id,
                                      data, partition_type, word_count);
  return retval;
}

bool flash_ctrl_testutils_read_page(
    dif_flash_ctrl_state_t *flash_state, uint32_t byte_address,
    uint32_t partition_id, uint32_t *data_out,
    dif_flash_ctrl_partition_type_t partition_type, uint32_t word_count,
    uint32_t delay) {
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
