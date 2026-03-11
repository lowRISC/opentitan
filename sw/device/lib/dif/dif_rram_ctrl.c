// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rram_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"

// Generated.
#include "hw/top/rram_ctrl_regs.h"

/**
 * Helper function to get the offset of a data region's configuration register.
 * Does not check that the region actually exists, which is deferred to callers.
 * Since data region registers are split into two (one containing properties the
 * other containing address info), there are two helper functions below.
 *
 * @param region The data region's index.
 * @return The offset from the RRAM controller's base address where the region
 * configuration register is located.
 */
OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_mp_reg_offset(uint32_t region) {
  return RRAM_CTRL_MP_REGION_CFG_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_reg_offset(uint32_t region) {
  return RRAM_CTRL_MP_REGION_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_lock_reg_offset(uint32_t region) {
  return RRAM_CTRL_REGION_CFG_REGWEN_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

// generated parameters from hjson
static const uint32_t kNumInfoPages = RRAM_CTRL_PARAM_NUM_INFO_PAGES;
static const uint32_t kNumDataPages = RRAM_CTRL_PARAM_NUM_DATA_PAGES;
static const uint32_t kBytesPerWord = RRAM_CTRL_PARAM_BYTES_PER_WORD;
static const uint32_t kBytesPerPage = RRAM_CTRL_PARAM_BYTES_PER_PAGE;
static const uint32_t kExecEn = RRAM_CTRL_PARAM_EXEC_EN;
static const uint32_t kNumRegions = RRAM_CTRL_PARAM_NUM_REGIONS;

/**
 * Helper function to get the offset of an info region's configuration register.
 * Does not check that the region actually exists, which is deferred to callers.
 *
 * @param region The info region's description.
 * @return The offset from the RRAM controller's base address where the region
 * configuration register is located.
 */
OT_WARN_UNUSED_RESULT
static ptrdiff_t get_info_region_mp_reg_offset(
    dif_rram_ctrl_info_region_t region) {
  return RRAM_CTRL_INFO_PAGE_CFG_0_REG_OFFSET +
         (ptrdiff_t)region.page * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_info_region_lock_reg_offset(
    dif_rram_ctrl_info_region_t region) {
  return RRAM_CTRL_INFO_REGWEN_0_REG_OFFSET +
         (ptrdiff_t)region.page * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_init_state(dif_rram_ctrl_state_t *handle,
                                      mmio_region_t base_addr) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  dif_result_t result = dif_rram_ctrl_init(base_addr, &handle->dev);
  if (result != kDifOk) {
    return result;
  }
  handle->words_remaining = 0;
  handle->transaction_pending = false;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_init_state_from_dt(dif_rram_ctrl_state_t *handle,
                                              dt_rram_ctrl_t dt) {
  return dif_rram_ctrl_init_state(
      handle, mmio_region_from_addr(dt_rram_ctrl_primary_reg_block(dt)));
}

OT_WARN_UNUSED_RESULT
dif_rram_ctrl_device_info_t dif_rram_ctrl_get_device_info(void) {
  const dif_rram_ctrl_device_info_t info = {
      .bytes_per_word = kBytesPerWord,
      .bytes_per_page = kBytesPerPage,
      .data_pages = kNumDataPages,
      .info_pages = kNumInfoPages,
  };
  return info;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_rram_enablement(dif_rram_ctrl_state_t *handle,
                                               dif_toggle_t enable) {
  enum multi_bit_bool disable_rram;
  if (handle == NULL) {
    return kDifBadArg;
  }
  switch (enable) {
    case kDifToggleEnabled:
      disable_rram = kMultiBitBool4False;
      break;
    case kDifToggleDisabled:
      disable_rram = kMultiBitBool4True;
      break;
    default:
      return kDifBadArg;
  }
  uint32_t reg;
  reg = mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_DIS_REG_OFFSET);
  reg = bitfield_field32_write(reg, RRAM_CTRL_DIS_SW_DIS_FIELD, disable_rram);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_DIS_REG_OFFSET, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_rram_enablement(
    const dif_rram_ctrl_state_t *handle, dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_DIS_REG_OFFSET);
  enum multi_bit_bool rram_disabled =
      bitfield_field32_read(reg, RRAM_CTRL_DIS_SW_DIS_FIELD);
  if (rram_disabled == kMultiBitBool4False) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_exec_enablement(dif_rram_ctrl_state_t *handle,
                                               dif_toggle_t enable) {
  uint32_t value;
  if (handle == NULL) {
    return kDifBadArg;
  }
  switch (enable) {
    case kDifToggleEnabled:
      value = kExecEn;
      break;
    case kDifToggleDisabled:
      value = 0;
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_EXEC_REG_OFFSET, value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_exec_enablement(
    const dif_rram_ctrl_state_t *handle, dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_EXEC_REG_OFFSET);
  if (reg == kExecEn) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_start_controller_init(
    dif_rram_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_INIT_REG_OFFSET);
  if (bitfield_bit32_read(reg, RRAM_CTRL_INIT_VAL_BIT)) {
    // Controller initialization may only be requested once.
    return kDifError;
  }
  uint32_t value = bitfield_bit32_write(0, RRAM_CTRL_INIT_VAL_BIT, true);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_INIT_REG_OFFSET, value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_status(const dif_rram_ctrl_state_t *handle,
                                      dif_rram_ctrl_status_t *status_out) {
  if (handle == NULL || status_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_STATUS_REG_OFFSET);
  dif_rram_ctrl_status_t status = {
      .read_fifo_full = bitfield_bit32_read(reg, RRAM_CTRL_STATUS_RD_FULL_BIT),
      .read_fifo_empty =
          bitfield_bit32_read(reg, RRAM_CTRL_STATUS_RD_EMPTY_BIT),
      .write_fifo_full = bitfield_bit32_read(reg, RRAM_CTRL_STATUS_WR_FULL_BIT),
      .write_fifo_empty =
          bitfield_bit32_read(reg, RRAM_CTRL_STATUS_WR_EMPTY_BIT),
      .controller_init_done =
          bitfield_bit32_read(reg, RRAM_CTRL_STATUS_INIT_DONE_BIT),
      .controller_keys_valid =
          bitfield_bit32_read(reg, RRAM_CTRL_STATUS_KEYS_VALID_BIT),
  };
  *status_out = status;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_start_unsafe(
    dif_rram_ctrl_state_t *handle, dif_rram_ctrl_transaction_t transaction) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl_regwen = mmio_region_read32(handle->dev.base_addr,
                                            RRAM_CTRL_CTRL_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(ctrl_regwen, RRAM_CTRL_CTRL_REGWEN_EN_BIT)) {
    return kDifUnavailable;
  }

  // Hardware ignores the NUM field for kDifRramCtrlOpRewrite (a rewrite always
  // affects exactly one word), so `transaction.word_count` is not meaningful
  // for that operation and isn't validated in `dif_rram_ctrl_start()`.
  uint32_t control_reg = bitfield_field32_write(0, RRAM_CTRL_CONTROL_NUM_FIELD,
                                                transaction.word_count - 1);
  switch (transaction.op) {
    case kDifRramCtrlOpRead:
      control_reg =
          bitfield_field32_write(control_reg, RRAM_CTRL_CONTROL_OP_FIELD,
                                 RRAM_CTRL_CONTROL_OP_VALUE_READ);
      break;
    case kDifRramCtrlOpWrite:
      control_reg =
          bitfield_field32_write(control_reg, RRAM_CTRL_CONTROL_OP_FIELD,
                                 RRAM_CTRL_CONTROL_OP_VALUE_WRITE);
      break;
    case kDifRramCtrlOpRewrite:
      control_reg =
          bitfield_field32_write(control_reg, RRAM_CTRL_CONTROL_OP_FIELD,
                                 RRAM_CTRL_CONTROL_OP_VALUE_REWRITE);
      break;
    default:
      return kDifBadArg;
  }

  switch (transaction.partition_type) {
    case kDifRramCtrlPartitionTypeData:
      control_reg = bitfield_bit32_write(
          control_reg, RRAM_CTRL_CONTROL_PARTITION_BIT, false);
      break;
    case kDifRramCtrlPartitionTypeInfo:
      control_reg = bitfield_bit32_write(control_reg,
                                         RRAM_CTRL_CONTROL_PARTITION_BIT, true);
      break;
    default:
      return kDifBadArg;
  }

  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_CONTROL_REG_OFFSET,
                      control_reg);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_ADDR_REG_OFFSET,
                      transaction.byte_address);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_CONTROL_REG_OFFSET,
                      control_reg | (1u << RRAM_CTRL_CONTROL_START_BIT));
  if (transaction.op == kDifRramCtrlOpRewrite) {
    // Rewrite operations don't use the FIFO
    handle->words_remaining = 0;
  } else {
    handle->words_remaining = transaction.word_count;
  }
  handle->transaction_pending = true;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_start(dif_rram_ctrl_state_t *handle,
                                 dif_rram_ctrl_transaction_t transaction) {
  if (handle == NULL) {
    return kDifBadArg;
  }

  const uint32_t max_word_count = RRAM_CTRL_CONTROL_NUM_MASK;
  if (transaction.op != kDifRramCtrlOpRewrite) {
    if (transaction.word_count - 1 > max_word_count ||
        transaction.word_count == 0) {
      return kDifBadArg;
    }
  }
  // We can only write a multiple of 4 32b words
  if (transaction.op == kDifRramCtrlOpWrite) {
    if (transaction.word_count % 4 != 0) {
      return kDifBadArg;
    }
  }

  // start address must be aligned to 16 bytes for write operations
  if (transaction.op == kDifRramCtrlOpWrite) {
    if (transaction.byte_address % 16 != 0) {
      return kDifBadArg;
    }
  }

  if (handle->transaction_pending) {
    return kDifUnavailable;
  }

  // Disallow starting a new transaction if the FIFOs haven't been emptied yet.
  dif_rram_ctrl_status_t status;
  dif_result_t result = dif_rram_ctrl_get_status(handle, &status);
  if (result != kDifOk) {
    return result;
  }
  if (!status.read_fifo_empty || !status.write_fifo_empty) {
    return kDifIpFifoFull;
  }

  return dif_rram_ctrl_start_unsafe(handle, transaction);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_wr_fifo_push_unsafe(dif_rram_ctrl_state_t *handle,
                                               uint32_t word_count,
                                               const uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  uint32_t written = 0;
  while (written < word_count) {
    mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_WR_FIFO_REG_OFFSET,
                        data[written]);
    ++written;
  }
  handle->words_remaining -= written;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_wr_fifo_push(dif_rram_ctrl_state_t *handle,
                                        uint32_t word_count,
                                        const uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  if (!handle->transaction_pending) {
    return kDifError;
  }
  if (handle->words_remaining < word_count) {
    return kDifBadArg;
  }
  const uint32_t control_reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_CONTROL_REG_OFFSET);
  const uint32_t op =
      bitfield_field32_read(control_reg, RRAM_CTRL_CONTROL_OP_FIELD);
  if (op != RRAM_CTRL_CONTROL_OP_VALUE_WRITE) {
    return kDifError;
  }
  return dif_rram_ctrl_wr_fifo_push_unsafe(handle, word_count, data);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_read_fifo_pop_unsafe(dif_rram_ctrl_state_t *handle,
                                                uint32_t word_count,
                                                uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  uint32_t read = 0;
  while (read < word_count) {
    data[read] =
        mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_RD_FIFO_REG_OFFSET);
    ++read;
  }
  handle->words_remaining -= read;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_read_fifo_pop(dif_rram_ctrl_state_t *handle,
                                         uint32_t word_count, uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  if (!handle->transaction_pending) {
    return kDifError;
  }
  if (handle->words_remaining < word_count) {
    return kDifBadArg;
  }
  const uint32_t control_reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_CONTROL_REG_OFFSET);
  const uint32_t op =
      bitfield_field32_read(control_reg, RRAM_CTRL_CONTROL_OP_FIELD);
  if (op != RRAM_CTRL_CONTROL_OP_VALUE_READ) {
    return kDifError;
  }
  return dif_rram_ctrl_read_fifo_pop_unsafe(handle, word_count, data);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_error_codes(
    const dif_rram_ctrl_state_t *handle,
    dif_rram_ctrl_error_t *error_code_out) {
  if (handle == NULL || error_code_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t code_reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_ERR_CODE_REG_OFFSET);
  dif_rram_ctrl_error_codes_t codes = {
      .operation_error =
          bitfield_bit32_read(code_reg, RRAM_CTRL_ERR_CODE_OP_ERR_BIT),
      .memory_protection_error =
          bitfield_bit32_read(code_reg, RRAM_CTRL_ERR_CODE_MP_ERR_BIT),
      .read_error =
          bitfield_bit32_read(code_reg, RRAM_CTRL_ERR_CODE_RD_ERR_BIT),
      .write_error =
          bitfield_bit32_read(code_reg, RRAM_CTRL_ERR_CODE_WR_ERR_BIT),
  };

  const uint32_t address_reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_ERR_ADDR_REG_OFFSET);
  dif_rram_ctrl_error_t error_code = {
      .address = address_reg,
      .codes = codes,
  };
  *error_code_out = error_code;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_clear_error_codes(
    dif_rram_ctrl_state_t *handle, dif_rram_ctrl_error_codes_t codes) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t code_reg = 0;
  code_reg = bitfield_bit32_write(code_reg, RRAM_CTRL_ERR_CODE_OP_ERR_BIT,
                                  codes.operation_error);
  code_reg = bitfield_bit32_write(code_reg, RRAM_CTRL_ERR_CODE_MP_ERR_BIT,
                                  codes.memory_protection_error);
  code_reg = bitfield_bit32_write(code_reg, RRAM_CTRL_ERR_CODE_RD_ERR_BIT,
                                  codes.read_error);
  code_reg = bitfield_bit32_write(code_reg, RRAM_CTRL_ERR_CODE_WR_ERR_BIT,
                                  codes.write_error);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_ERR_CODE_REG_OFFSET,
                      code_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_end(dif_rram_ctrl_state_t *handle,
                               dif_rram_ctrl_output_t *out) {
  if (handle == NULL || out == NULL) {
    return kDifBadArg;
  }
  if (!handle->transaction_pending) {
    return kDifError;
  }
  uint32_t status_reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_OP_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status_reg, RRAM_CTRL_OP_STATUS_DONE_BIT)) {
    return kDifUnavailable;
  }
  if (handle->words_remaining != 0) {
    return kDifIpFifoFull;
  }
  dif_rram_ctrl_error_t error_code_tmp;
  DIF_RETURN_IF_ERROR(dif_rram_ctrl_get_error_codes(handle, &error_code_tmp));
  dif_rram_ctrl_output_t output = {
      .operation_done =
          bitfield_bit32_read(status_reg, RRAM_CTRL_OP_STATUS_DONE_BIT),
      .operation_error =
          bitfield_bit32_read(status_reg, RRAM_CTRL_OP_STATUS_ERR_BIT),
      .error_code = error_code_tmp};
  // Clear the operation status
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_OP_STATUS_REG_OFFSET, 0);
  handle->transaction_pending = false;
  *out = output;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_data_region_enablement(
    dif_rram_ctrl_state_t *handle, uint32_t region, dif_toggle_t enable) {
  if (handle == NULL || region >= kNumRegions) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  switch (enable) {
    case kDifToggleEnabled:
      mp_reg = bitfield_field32_write(
          mp_reg, RRAM_CTRL_MP_REGION_CFG_0_EN_0_FIELD, kMultiBitBool4True);
      break;
    case kDifToggleDisabled:
      mp_reg = bitfield_field32_write(
          mp_reg, RRAM_CTRL_MP_REGION_CFG_0_EN_0_FIELD, kMultiBitBool4False);
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, mp_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_data_region_enablement(
    const dif_rram_ctrl_state_t *handle, uint32_t region,
    dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL || region >= kNumRegions) {
    return kDifBadArg;
  }
  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  if (bitfield_field32_read(mp_reg, RRAM_CTRL_MP_REGION_CFG_0_EN_0_FIELD) ==
      kMultiBitBool4True) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_info_region_enablement(
    dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region,
    dif_toggle_t enable) {
  if (handle == NULL || region.page >= kNumInfoPages) {
    return kDifBadArg;
  }
  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  switch (enable) {
    case kDifToggleEnabled:
      mp_reg = bitfield_field32_write(
          mp_reg, RRAM_CTRL_INFO_PAGE_CFG_0_EN_0_FIELD, kMultiBitBool4True);
      break;
    case kDifToggleDisabled:
      mp_reg = bitfield_field32_write(
          mp_reg, RRAM_CTRL_INFO_PAGE_CFG_0_EN_0_FIELD, kMultiBitBool4False);
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, mp_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_info_region_enablement(
    const dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region,
    dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL || region.page >= kNumInfoPages) {
    return kDifBadArg;
  }
  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  if (bitfield_field32_read(mp_reg, RRAM_CTRL_INFO_PAGE_CFG_0_EN_0_FIELD) ==
      kMultiBitBool4True) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_default_region_properties(
    dif_rram_ctrl_state_t *handle,
    dif_rram_ctrl_region_properties_t properties) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, RRAM_CTRL_DEFAULT_REGION_RD_EN_FIELD,
                               properties.rd_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_DEFAULT_REGION_WR_EN_FIELD,
                               properties.wr_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD,
                               properties.scramble_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_DEFAULT_REGION_ECC_EN_FIELD,
                               properties.ecc_en);
  mmio_region_write32(handle->dev.base_addr,
                      RRAM_CTRL_DEFAULT_REGION_REG_OFFSET, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_default_region_properties(
    const dif_rram_ctrl_state_t *handle,
    dif_rram_ctrl_region_properties_t *properties_out) {
  if (handle == NULL || properties_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                          RRAM_CTRL_DEFAULT_REGION_REG_OFFSET);
  dif_rram_ctrl_region_properties_t properties = {
      .rd_en = bitfield_field32_read(reg, RRAM_CTRL_DEFAULT_REGION_RD_EN_FIELD),
      .wr_en = bitfield_field32_read(reg, RRAM_CTRL_DEFAULT_REGION_WR_EN_FIELD),
      .scramble_en = bitfield_field32_read(
          reg, RRAM_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD),
      .ecc_en =
          bitfield_field32_read(reg, RRAM_CTRL_DEFAULT_REGION_ECC_EN_FIELD),
  };
  *properties_out = properties;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_data_region_properties(
    dif_rram_ctrl_state_t *handle, uint32_t region,
    dif_rram_ctrl_data_region_properties_t config) {
  const uint32_t page_limit = kNumDataPages;
  if (handle == NULL || region >= kNumRegions ||
      config.base + config.size > page_limit) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  reg = bitfield_field32_write(reg, RRAM_CTRL_MP_REGION_CFG_0_RD_EN_0_FIELD,
                               config.properties.rd_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_MP_REGION_CFG_0_WR_EN_0_FIELD,
                               config.properties.wr_en);
  reg =
      bitfield_field32_write(reg, RRAM_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_FIELD,
                             config.properties.scramble_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_MP_REGION_CFG_0_ECC_EN_0_FIELD,
                               config.properties.ecc_en);

  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);

  // size and base are stored in different registers
  mp_reg_offset = get_data_region_reg_offset(region);

  reg = bitfield_field32_write(0, RRAM_CTRL_MP_REGION_0_BASE_0_FIELD,
                               config.base);
  reg = bitfield_field32_write(reg, RRAM_CTRL_MP_REGION_0_SIZE_0_FIELD,
                               config.size);
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_data_region_properties(
    const dif_rram_ctrl_state_t *handle, uint32_t region,
    dif_rram_ctrl_data_region_properties_t *config_out) {
  if (handle == NULL || config_out == NULL || region >= kNumRegions) {
    return kDifBadArg;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  dif_rram_ctrl_data_region_properties_t config;
  config.properties.rd_en =
      bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_CFG_0_RD_EN_0_FIELD);
  config.properties.wr_en =
      bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_CFG_0_WR_EN_0_FIELD);
  config.properties.scramble_en =
      bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_FIELD);
  config.properties.ecc_en =
      bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_CFG_0_ECC_EN_0_FIELD);

  mp_reg_offset = get_data_region_reg_offset(region);
  reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  config.base = bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_0_BASE_0_FIELD);
  config.size = bitfield_field32_read(reg, RRAM_CTRL_MP_REGION_0_SIZE_0_FIELD);
  *config_out = config;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_info_region_properties(
    dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region,
    dif_rram_ctrl_region_properties_t properties) {
  if (handle == NULL || region.page >= kNumInfoPages) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  reg = bitfield_field32_write(reg, RRAM_CTRL_INFO_PAGE_CFG_0_RD_EN_0_FIELD,
                               properties.rd_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_INFO_PAGE_CFG_0_WR_EN_0_FIELD,
                               properties.wr_en);
  reg =
      bitfield_field32_write(reg, RRAM_CTRL_INFO_PAGE_CFG_0_SCRAMBLE_EN_0_FIELD,
                             properties.scramble_en);
  reg = bitfield_field32_write(reg, RRAM_CTRL_INFO_PAGE_CFG_0_ECC_EN_0_FIELD,
                               properties.ecc_en);
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_info_region_properties(
    const dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region,
    dif_rram_ctrl_region_properties_t *properties_out) {
  if (handle == NULL || properties_out == NULL ||
      region.page >= kNumInfoPages) {
    return kDifBadArg;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  dif_rram_ctrl_region_properties_t properties;
  properties.rd_en =
      bitfield_field32_read(reg, RRAM_CTRL_INFO_PAGE_CFG_0_RD_EN_0_FIELD);
  properties.wr_en =
      bitfield_field32_read(reg, RRAM_CTRL_INFO_PAGE_CFG_0_WR_EN_0_FIELD);
  properties.scramble_en =
      bitfield_field32_read(reg, RRAM_CTRL_INFO_PAGE_CFG_0_SCRAMBLE_EN_0_FIELD);
  properties.ecc_en =
      bitfield_field32_read(reg, RRAM_CTRL_INFO_PAGE_CFG_0_ECC_EN_0_FIELD);
  *properties_out = properties;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_lock_data_region_properties(
    dif_rram_ctrl_state_t *handle, uint32_t region) {
  if (handle == NULL || region >= kNumRegions) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t lock_reg_offset = get_data_region_lock_reg_offset(region);
  uint32_t reg = bitfield_bit32_write(
      0, RRAM_CTRL_REGION_CFG_REGWEN_0_REGION_0_BIT, false);
  mmio_region_write32(handle->dev.base_addr, lock_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_lock_info_region_properties(
    dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region) {
  if (handle == NULL || region.page >= kNumInfoPages) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_rram_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t lock_reg_offset = get_info_region_lock_reg_offset(region);
  uint32_t reg =
      bitfield_bit32_write(0, RRAM_CTRL_INFO_REGWEN_0_REGION_0_BIT, false);
  mmio_region_write32(handle->dev.base_addr, lock_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_data_region_is_locked(
    const dif_rram_ctrl_state_t *handle, uint32_t region, bool *locked_out) {
  if (handle == NULL || locked_out == NULL || region >= kNumRegions) {
    return kDifBadArg;
  }
  ptrdiff_t lock_reg_offset = get_data_region_lock_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, lock_reg_offset);
  *locked_out =
      !bitfield_bit32_read(reg, RRAM_CTRL_REGION_CFG_REGWEN_0_REGION_0_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_info_region_is_locked(
    const dif_rram_ctrl_state_t *handle, dif_rram_ctrl_info_region_t region,
    bool *locked_out) {
  if (handle == NULL || locked_out == NULL || region.page >= kNumInfoPages) {
    return kDifBadArg;
  }

  ptrdiff_t lock_reg_offset = get_info_region_lock_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, lock_reg_offset);
  *locked_out = !bitfield_bit32_read(reg, RRAM_CTRL_INFO_REGWEN_0_REGION_0_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_wr_fifo_watermark(dif_rram_ctrl_state_t *handle,
                                                 uint32_t level) {
  if (handle == NULL || level > RRAM_CTRL_FIFO_LVL_WR_MASK) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_FIFO_LVL_REG_OFFSET);
  reg = bitfield_field32_write(reg, RRAM_CTRL_FIFO_LVL_WR_FIELD, level);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_FIFO_LVL_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_read_fifo_watermark(
    dif_rram_ctrl_state_t *handle, uint32_t level) {
  if (handle == NULL || level > RRAM_CTRL_FIFO_LVL_RD_MASK) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_FIFO_LVL_REG_OFFSET);
  reg = bitfield_field32_write(reg, RRAM_CTRL_FIFO_LVL_RD_FIELD, level);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_FIFO_LVL_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_fifo_watermarks(
    const dif_rram_ctrl_state_t *handle, uint32_t *write_out,
    uint32_t *read_out) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_FIFO_LVL_REG_OFFSET);
  if (write_out != NULL) {
    *write_out = bitfield_field32_read(reg, RRAM_CTRL_FIFO_LVL_WR_FIELD);
  }
  if (read_out != NULL) {
    *read_out = bitfield_field32_read(reg, RRAM_CTRL_FIFO_LVL_RD_FIELD);
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_clear_wr_fifo(dif_rram_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = bitfield_bit32_write(0, RRAM_CTRL_FIFO_CLR_WR_BIT, true);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_FIFO_CLR_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_clear_rd_fifo(dif_rram_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = bitfield_bit32_write(0, RRAM_CTRL_FIFO_CLR_RD_BIT, true);
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_FIFO_CLR_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_faults(const dif_rram_ctrl_state_t *handle,
                                      dif_rram_ctrl_faults_t *faults_out) {
  if (handle == NULL || faults_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    RRAM_CTRL_FAULT_STATUS_REG_OFFSET);
  dif_rram_ctrl_faults_t faults;
  faults.lcmgr_operation_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_LCMGR_OP_ERR_BIT);
  faults.lcmgr_memory_protection_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_LCMGR_MP_ERR_BIT);
  faults.lcmgr_read_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_LCMGR_RD_ERR_BIT);
  faults.lcmgr_write_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_LCMGR_WR_ERR_BIT);
  faults.otp_operation_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_OTP_OP_ERR_BIT);
  faults.otp_memory_protection_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_OTP_MP_ERR_BIT);
  faults.otp_read_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_OTP_RD_ERR_BIT);
  faults.otp_write_error =
      bitfield_bit32_read(reg, RRAM_CTRL_FAULT_STATUS_OTP_WR_ERR_BIT);
  // TODO: Add more faults?
  *faults_out = faults;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_ecc_errors(
    const dif_rram_ctrl_state_t *handle,
    dif_rram_ctrl_ecc_errors_t *errors_out) {
  if (handle == NULL || errors_out == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    RRAM_CTRL_CORR_ERR_CNT_REG_OFFSET);
  errors_out->corr_error_count =
      bitfield_field32_read(reg, RRAM_CTRL_CORR_ERR_CNT_VAL_FIELD);

  reg = mmio_region_read32(handle->dev.base_addr,
                           RRAM_CTRL_CORR_ERR_LOC_REG_OFFSET);

  errors_out->last_error_address =
      bitfield_field32_read(reg, RRAM_CTRL_CORR_ERR_LOC_ADDR_FIELD);
  errors_out->last_error_partition =
      bitfield_bit32_read(reg, RRAM_CTRL_CORR_ERR_LOC_PART_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_phy_status(
    const dif_rram_ctrl_state_t *handle,
    dif_rram_ctrl_phy_status_t *status_out) {
  if (handle == NULL || status_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                          RRAM_CTRL_PHY_STATUS_REG_OFFSET);
  dif_rram_ctrl_phy_status_t status = {
      .phy_init_done =
          bitfield_bit32_read(reg, RRAM_CTRL_PHY_STATUS_INIT_DONE_BIT),
      .phy_wr_busy = bitfield_bit32_read(reg, RRAM_CTRL_PHY_STATUS_WR_BUSY_BIT),
  };
  *status_out = status;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_set_scratch(dif_rram_ctrl_state_t *handle,
                                       uint32_t value) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, RRAM_CTRL_SCRATCH_REG_OFFSET,
                      value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_rram_ctrl_get_scratch(const dif_rram_ctrl_state_t *handle,
                                       uint32_t *value_out) {
  if (handle == NULL || value_out == NULL) {
    return kDifBadArg;
  }
  *value_out =
      mmio_region_read32(handle->dev.base_addr, RRAM_CTRL_SCRATCH_REG_OFFSET);
  return kDifOk;
}
