// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rram_ctrl_testutils.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rram_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top/rram_ctrl_regs.h"  // Generated

#define MODULE_ID MAKE_MODULE_ID('r', 'c', 't')

status_t rram_ctrl_testutils_wait_for_init(dif_rram_ctrl_state_t *rram_state) {
  dif_rram_ctrl_status_t status;
  do {
    TRY(dif_rram_ctrl_get_status(rram_state, &status));
  } while (status.controller_init_done == 0);
  return OK_STATUS();
}

status_t rram_ctrl_testutils_wait_transaction_end(
    dif_rram_ctrl_state_t *rram_state) {
  dif_rram_ctrl_output_t output;
  dif_result_t dif_result;
  do {
    dif_result = dif_rram_ctrl_end(rram_state, &output);
    TRY_CHECK(dif_result != kDifBadArg);
    TRY_CHECK(dif_result != kDifError);
  } while (dif_result != kDifOk);

  if (output.operation_error) {
    dif_rram_ctrl_error_codes_t codes = output.error_code.codes;
    uint32_t error_reg = 0;
    error_reg = bitfield_bit32_write(error_reg, RRAM_CTRL_ERR_CODE_OP_ERR_BIT,
                                     codes.operation_error);
    error_reg = bitfield_bit32_write(error_reg, RRAM_CTRL_ERR_CODE_MP_ERR_BIT,
                                     codes.memory_protection_error);
    error_reg = bitfield_bit32_write(error_reg, RRAM_CTRL_ERR_CODE_RD_ERR_BIT,
                                     codes.read_error);
    error_reg = bitfield_bit32_write(error_reg, RRAM_CTRL_ERR_CODE_WR_ERR_BIT,
                                     codes.write_error);
  }
  TRY(dif_rram_ctrl_clear_error_codes(rram_state, output.error_code.codes));
  return output.operation_error == 0 ? OK_STATUS() : INTERNAL();
}

status_t rram_ctrl_testutils_data_region_setup_properties(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size,
    dif_rram_ctrl_region_properties_t region_properties, uint32_t *offset) {
  dif_rram_ctrl_data_region_properties_t data_region_properties = {
      .base = base_page_index,
      .properties = region_properties,
      .size = region_size};

  TRY(dif_rram_ctrl_set_data_region_properties(rram_state, data_region,
                                               data_region_properties));
  TRY(dif_rram_ctrl_set_data_region_enablement(rram_state, data_region,
                                               kDifToggleEnabled));

  if (offset != NULL) {
    dif_rram_ctrl_device_info_t device_info = dif_rram_ctrl_get_device_info();
    *offset = base_page_index * device_info.bytes_per_page;
  }
  return OK_STATUS();
}

status_t rram_ctrl_testutils_data_region_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset) {
  dif_rram_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .wr_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False};
  return rram_ctrl_testutils_data_region_setup_properties(
      rram_state, base_page_index, data_region, region_size, region_properties,
      offset);
}

status_t rram_ctrl_testutils_data_region_scrambled_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t base_page_index,
    uint32_t data_region, uint32_t region_size, uint32_t *offset) {
  dif_rram_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .wr_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True};
  return rram_ctrl_testutils_data_region_setup_properties(
      rram_state, base_page_index, data_region, region_size, region_properties,
      offset);
}

status_t rram_ctrl_testutils_info_region_setup_properties(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id,
    dif_rram_ctrl_region_properties_t region_properties, uint32_t *offset) {
  dif_rram_ctrl_info_region_t info_region = {.page = page_id};

  TRY(dif_rram_ctrl_set_info_region_properties(rram_state, info_region,
                                               region_properties));
  TRY(dif_rram_ctrl_set_info_region_enablement(rram_state, info_region,
                                               kDifToggleEnabled));

  if (offset != NULL) {
    dif_rram_ctrl_device_info_t device_info = dif_rram_ctrl_get_device_info();
    *offset = page_id * device_info.bytes_per_page;
  }
  return OK_STATUS();
}

status_t rram_ctrl_testutils_info_region_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id, uint32_t *offset) {
  dif_rram_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .wr_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False};
  return rram_ctrl_testutils_info_region_setup_properties(
      rram_state, page_id, region_properties, offset);
}

status_t rram_ctrl_testutils_info_region_scrambled_setup(
    dif_rram_ctrl_state_t *rram_state, uint32_t page_id, uint32_t *offset) {
  dif_rram_ctrl_region_properties_t region_properties = {
      .ecc_en = kMultiBitBool4True,
      .wr_en = kMultiBitBool4True,
      .rd_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4True};
  return rram_ctrl_testutils_info_region_setup_properties(
      rram_state, page_id, region_properties, offset);
}

status_t rram_ctrl_testutils_write(
    dif_rram_ctrl_state_t *rram_state, uint32_t byte_address,
    const uint32_t *data, dif_rram_ctrl_partition_type_t partition_type,
    uint32_t word_count) {
  dif_rram_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                             .op = kDifRramCtrlOpWrite,
                                             .partition_type = partition_type,
                                             .word_count = 0x0};
  uint32_t words_written = 0;
  uint32_t word_address = byte_address / sizeof(uint32_t);
  const uint32_t max_words = (uint32_t)RRAM_CTRL_CONTROL_NUM_MASK + 1;

  status_t status = OK_STATUS();
  while (words_written < word_count) {
    uint32_t words_remaining = word_count - words_written;
    uint32_t words_to_write =
        (words_remaining < max_words) ? words_remaining : max_words;
    transaction.byte_address = word_address * sizeof(uint32_t);
    transaction.word_count = words_to_write;
    TRY(dif_rram_ctrl_start(rram_state, transaction));
    TRY(dif_rram_ctrl_wr_fifo_push(rram_state, words_to_write,
                                   data + words_written));
    status = rram_ctrl_testutils_wait_transaction_end(rram_state);
    word_address += words_to_write;
    words_written += words_to_write;
  }
  return status;
}

status_t rram_ctrl_testutils_write_word(
    dif_rram_ctrl_state_t *rram_state, uint32_t byte_address,
    const uint32_t *data, dif_rram_ctrl_partition_type_t partition_type) {
  dif_rram_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                             .op = kDifRramCtrlOpWrite,
                                             .partition_type = partition_type,
                                             .word_count = 0x0};
  uint32_t word_addr_aligned = byte_address & ~(uintptr_t)0xF;
  uint32_t word_idx = (byte_address >> 2) % 4;

  status_t status = OK_STATUS();

  uint32_t data_short[4];
  CHECK_STATUS_OK(rram_ctrl_testutils_read(rram_state, word_addr_aligned,
                                           data_short, partition_type, 4, 0));
  data_short[word_idx] = *data;

  transaction.byte_address = word_addr_aligned;
  transaction.word_count = 4;
  TRY(dif_rram_ctrl_start(rram_state, transaction));
  TRY(dif_rram_ctrl_wr_fifo_push(rram_state, 4, data_short));
  status = rram_ctrl_testutils_wait_transaction_end(rram_state);
  return status;
}

status_t rram_ctrl_testutils_read(dif_rram_ctrl_state_t *rram_state,
                                  uint32_t byte_address, uint32_t *data_out,
                                  dif_rram_ctrl_partition_type_t partition_type,
                                  uint32_t word_count, uint32_t delay_micros) {
  dif_rram_ctrl_transaction_t transaction = {.byte_address = byte_address,
                                             .op = kDifRramCtrlOpRead,
                                             .partition_type = partition_type,
                                             .word_count = word_count};

  // Read Page.
  TRY(dif_rram_ctrl_start(rram_state, transaction));
  // Optional delay to allow for read fifo fill testing.
  busy_spin_micros(delay_micros);
  TRY(dif_rram_ctrl_read_fifo_pop(rram_state, word_count, data_out));
  return rram_ctrl_testutils_wait_transaction_end(rram_state);
}

status_t rram_ctrl_testutils_default_region_access(
    dif_rram_ctrl_state_t *rram_state, bool rd_en, bool wr_en, bool scramble_en,
    bool ecc_en) {
  dif_rram_ctrl_region_properties_t default_properties = {
      .rd_en = rd_en ? kMultiBitBool4True : kMultiBitBool4False,
      .wr_en = wr_en ? kMultiBitBool4True : kMultiBitBool4False,
      .scramble_en = scramble_en ? kMultiBitBool4True : kMultiBitBool4False,
      .ecc_en = ecc_en ? kMultiBitBool4True : kMultiBitBool4False};

  TRY(dif_rram_ctrl_set_default_region_properties(rram_state,
                                                  default_properties));
  return OK_STATUS();
}

status_t rram_ctrl_testutils_show_faults(
    const dif_rram_ctrl_state_t *rram_ctrl) {
  dif_rram_ctrl_faults_t faults = {.lcmgr_memory_protection_error = false};
  CHECK_DIF_OK(dif_rram_ctrl_get_faults(rram_ctrl, &faults));
#define LOG_IF_FIELD_SET(_struct, _field)             \
  if (_struct._field != 0) {                          \
    LOG_INFO("rram_ctrl  fault status has " #_field); \
  }

  LOG_IF_FIELD_SET(faults, lcmgr_operation_error);
  LOG_IF_FIELD_SET(faults, lcmgr_memory_protection_error);
  LOG_IF_FIELD_SET(faults, lcmgr_read_error);
  LOG_IF_FIELD_SET(faults, lcmgr_write_error);
#undef LOG_IF_FIELD_SET

  return OK_STATUS();
}

static const char *mubi_prop(multi_bit_bool_t val, const char *name) {
  switch (val) {
    case kMultiBitBool4True:
      return name;
    case kMultiBitBool4False:
      return "xx";
    default:
      return "uu";
  }
}

void rram_ctrl_testutils_data_region_print(
    size_t index, dif_rram_ctrl_data_region_properties_t *p, bool locked) {
  LOG_INFO("data region n=%u st=%u sz=%u %s-%s-%s-%s %s", index, p->base,
           p->size, mubi_prop(p->properties.rd_en, "RD"),
           mubi_prop(p->properties.wr_en, "WR"),
           mubi_prop(p->properties.scramble_en, "SC"),
           mubi_prop(p->properties.ecc_en, "EC"), locked ? "LK" : "UN");
}

void rram_ctrl_testutils_info_region_print(dif_rram_ctrl_info_region_t region,
                                           dif_rram_ctrl_region_properties_t *p,
                                           bool locked) {
  LOG_INFO("info region page=%u %s-%s-%s-%s %s", region.page,
           mubi_prop(p->rd_en, "RD"), mubi_prop(p->wr_en, "WR"),
           mubi_prop(p->scramble_en, "SC"), mubi_prop(p->ecc_en, "EC"),
           locked ? "LK" : "UN");
}
