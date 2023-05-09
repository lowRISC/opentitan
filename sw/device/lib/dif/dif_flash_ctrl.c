// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_flash_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"

// Generated.
#include "flash_ctrl_regs.h"

/**
 * Helper function to get the offset of a data region's configuration register.
 * Does not check that the region actually exists, which is deferred to callers.
 * Since data region registers are split into two (one containing properties the
 * other containing address info), there are two helper functions below.
 *
 * @param region The data region's index.
 * @return The offset from the flash controller's base address where the region
 * configuration register is located.
 */
OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_mp_reg_offset(uint32_t region) {
  return FLASH_CTRL_MP_REGION_CFG_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_reg_offset(uint32_t region) {
  return FLASH_CTRL_MP_REGION_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_data_region_lock_reg_offset(uint32_t region) {
  return FLASH_CTRL_REGION_CFG_REGWEN_0_REG_OFFSET +
         (ptrdiff_t)region * (ptrdiff_t)sizeof(uint32_t);
}

// The info region register tables have contents that depend on a particular
// number of flash banks. If that number changes, the tables will need to be
// updated.
static_assert(FLASH_CTRL_PARAM_REG_NUM_BANKS == 2,
              "Please update the info region register tables.");

// TODO: Can we populate the number of info partition types in the header too?
// The number of different types of info regions.
#ifndef FLASH_CTRL_NUM_INFO_TYPES
#define FLASH_CTRL_NUM_INFO_TYPES 3
#endif

// A more convenient mapping between the info regions and their configuration
// register offset.
static const ptrdiff_t
    kInfoConfigOffsets[FLASH_CTRL_NUM_INFO_TYPES]
                      [FLASH_CTRL_PARAM_REG_NUM_BANKS] = {
                          {
                              FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_REG_OFFSET,
                              FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_REG_OFFSET,
                          },
                          {
                              FLASH_CTRL_BANK0_INFO1_PAGE_CFG_REG_OFFSET,
                              FLASH_CTRL_BANK1_INFO1_PAGE_CFG_REG_OFFSET,
                          },
                          {
                              FLASH_CTRL_BANK0_INFO2_PAGE_CFG_0_REG_OFFSET,
                              FLASH_CTRL_BANK1_INFO2_PAGE_CFG_0_REG_OFFSET,
                          },
};

static const ptrdiff_t
    kInfoLockOffsets[FLASH_CTRL_NUM_INFO_TYPES]
                    [FLASH_CTRL_PARAM_REG_NUM_BANKS] = {
                        {
                            FLASH_CTRL_BANK0_INFO0_REGWEN_0_REG_OFFSET,
                            FLASH_CTRL_BANK1_INFO0_REGWEN_0_REG_OFFSET,
                        },
                        {
                            FLASH_CTRL_BANK0_INFO1_REGWEN_REG_OFFSET,
                            FLASH_CTRL_BANK1_INFO1_REGWEN_REG_OFFSET,
                        },
                        {
                            FLASH_CTRL_BANK0_INFO2_REGWEN_0_REG_OFFSET,
                            FLASH_CTRL_BANK1_INFO2_REGWEN_0_REG_OFFSET,
                        },
};

static const uint32_t kNumInfoPagesPerBank[FLASH_CTRL_NUM_INFO_TYPES] = {
    FLASH_CTRL_PARAM_NUM_INFOS0,
    FLASH_CTRL_PARAM_NUM_INFOS1,
    FLASH_CTRL_PARAM_NUM_INFOS2,
};

/**
 * Helper function to get the offset of an info region's configuration register.
 * Does not check that the region actually exists, which is deferred to callers.
 *
 * @param region The info region's description.
 * @return The offset from the flash controller's base address where the region
 * configuration register is located.
 */
OT_WARN_UNUSED_RESULT
static ptrdiff_t get_info_region_mp_reg_offset(
    dif_flash_ctrl_info_region_t region) {
  return kInfoConfigOffsets[region.partition_id][region.bank] +
         (ptrdiff_t)region.page * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
static ptrdiff_t get_info_region_lock_reg_offset(
    dif_flash_ctrl_info_region_t region) {
  return kInfoLockOffsets[region.partition_id][region.bank] +
         (ptrdiff_t)region.page * (ptrdiff_t)sizeof(uint32_t);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_init_state(dif_flash_ctrl_state_t *handle,
                                       mmio_region_t base_addr) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  dif_result_t result = dif_flash_ctrl_init(base_addr, &handle->dev);
  if (result != kDifOk) {
    return result;
  }
  handle->words_remaining = 0;
  handle->transaction_pending = false;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_flash_ctrl_device_info_t dif_flash_ctrl_get_device_info(void) {
  const dif_flash_ctrl_device_info_t info = {
      .num_banks = FLASH_CTRL_PARAM_REG_NUM_BANKS,
      .bytes_per_word = FLASH_CTRL_PARAM_BYTES_PER_WORD,
      .bytes_per_page = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
      .data_pages = FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,
      .info0_pages = FLASH_CTRL_PARAM_NUM_INFOS0,
      .info1_pages = FLASH_CTRL_PARAM_NUM_INFOS1,
      .info2_pages = FLASH_CTRL_PARAM_NUM_INFOS2,
  };
  return info;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_flash_enablement(dif_flash_ctrl_state_t *handle,
                                                 dif_toggle_t enable) {
  enum multi_bit_bool disable_flash;
  if (handle == NULL) {
    return kDifBadArg;
  }
  // TODO: Get agreement on how multi-bit bools are used. This register has
  // negative logic for dif_toggle_t and treats "invalid" values differently
  // from the typical "true => enable" registers.
  switch (enable) {
    case kDifToggleEnabled:
      disable_flash = kMultiBitBool4False;
      break;
    case kDifToggleDisabled:
      disable_flash = kMultiBitBool4True;
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_DIS_REG_OFFSET,
                      disable_flash);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_flash_enablement(
    const dif_flash_ctrl_state_t *handle, dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_DIS_REG_OFFSET);
  enum multi_bit_bool flash_disabled =
      bitfield_field32_read(reg, FLASH_CTRL_DIS_VAL_FIELD);
  // TODO: As above, determine if there is a convention for multi-bit bools
  // where "true => disable", and consider creating a common function to handle
  // conversion.
  if (flash_disabled == kMultiBitBool4False) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_exec_enablement(dif_flash_ctrl_state_t *handle,
                                                dif_toggle_t enable) {
  uint32_t value;
  if (handle == NULL) {
    return kDifBadArg;
  }
  switch (enable) {
    case kDifToggleEnabled:
      value = FLASH_CTRL_PARAM_EXEC_EN;
      break;
    case kDifToggleDisabled:
      value = 0;
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_EXEC_REG_OFFSET, value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_exec_enablement(
    const dif_flash_ctrl_state_t *handle, dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_EXEC_REG_OFFSET);
  if (reg == FLASH_CTRL_PARAM_EXEC_EN) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_start_controller_init(
    dif_flash_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_INIT_REG_OFFSET);
  if (bitfield_bit32_read(reg, FLASH_CTRL_INIT_VAL_BIT)) {
    // Controller initialization may only be requested once.
    return kDifError;
  }
  uint32_t value = bitfield_bit32_write(0, FLASH_CTRL_INIT_VAL_BIT, true);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_INIT_REG_OFFSET, value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_status(const dif_flash_ctrl_state_t *handle,
                                       dif_flash_ctrl_status_t *status_out) {
  if (handle == NULL || status_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_STATUS_REG_OFFSET);
  dif_flash_ctrl_status_t status = {
      .read_fifo_full = bitfield_bit32_read(reg, FLASH_CTRL_STATUS_RD_FULL_BIT),
      .read_fifo_empty =
          bitfield_bit32_read(reg, FLASH_CTRL_STATUS_RD_EMPTY_BIT),
      .prog_fifo_full =
          bitfield_bit32_read(reg, FLASH_CTRL_STATUS_PROG_FULL_BIT),
      .prog_fifo_empty =
          bitfield_bit32_read(reg, FLASH_CTRL_STATUS_PROG_EMPTY_BIT),
      .controller_init_wip =
          bitfield_bit32_read(reg, FLASH_CTRL_STATUS_INIT_WIP_BIT),
  };
  *status_out = status;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_allowed_prog_types(
    const dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_prog_capabilities_t *allowed_types_out) {
  if (handle == NULL || allowed_types_out == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET);
  dif_flash_ctrl_prog_capabilities_t allowed_types = {
      .normal_prog_type =
          bitfield_bit32_read(reg, FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT),
      .repair_prog_type =
          bitfield_bit32_read(reg, FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT),
  };
  *allowed_types_out = allowed_types;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_disallow_prog_types(
    dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_prog_capabilities_t types_to_disallow) {
  if (handle == NULL) {
    return kDifBadArg;
  }

  uint32_t ctrl_regwen = mmio_region_read32(handle->dev.base_addr,
                                            FLASH_CTRL_CTRL_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(ctrl_regwen, FLASH_CTRL_CTRL_REGWEN_EN_BIT)) {
    return kDifUnavailable;
  }

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, FLASH_CTRL_PROG_TYPE_EN_NORMAL_BIT,
                             !types_to_disallow.normal_prog_type);
  reg = bitfield_bit32_write(reg, FLASH_CTRL_PROG_TYPE_EN_REPAIR_BIT,
                             !types_to_disallow.repair_prog_type);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_PROG_TYPE_EN_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_start_unsafe(
    dif_flash_ctrl_state_t *handle, dif_flash_ctrl_transaction_t transaction) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t ctrl_regwen = mmio_region_read32(handle->dev.base_addr,
                                            FLASH_CTRL_CTRL_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(ctrl_regwen, FLASH_CTRL_CTRL_REGWEN_EN_BIT)) {
    return kDifUnavailable;
  }

  uint32_t control_reg = bitfield_field32_write(0, FLASH_CTRL_CONTROL_NUM_FIELD,
                                                transaction.word_count - 1);
  switch (transaction.op) {
    case kDifFlashCtrlOpRead:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_OP_FIELD,
                                 FLASH_CTRL_CONTROL_OP_VALUE_READ);
      break;
    case kDifFlashCtrlOpProgram:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_OP_FIELD,
                                 FLASH_CTRL_CONTROL_OP_VALUE_PROG);
      control_reg = bitfield_bit32_write(
          control_reg, FLASH_CTRL_CONTROL_PROG_SEL_BIT, false);
      break;
    case kDifFlashCtrlOpProgramRepair:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_OP_FIELD,
                                 FLASH_CTRL_CONTROL_OP_VALUE_PROG);
      control_reg = bitfield_bit32_write(control_reg,
                                         FLASH_CTRL_CONTROL_PROG_SEL_BIT, true);
      break;
    case kDifFlashCtrlOpPageErase:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_OP_FIELD,
                                 FLASH_CTRL_CONTROL_OP_VALUE_ERASE);
      control_reg = bitfield_bit32_write(
          control_reg, FLASH_CTRL_CONTROL_ERASE_SEL_BIT, false);
      break;
    case kDifFlashCtrlOpBankErase:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_OP_FIELD,
                                 FLASH_CTRL_CONTROL_OP_VALUE_ERASE);
      control_reg = bitfield_bit32_write(
          control_reg, FLASH_CTRL_CONTROL_ERASE_SEL_BIT, true);
      break;
    default:
      return kDifBadArg;
  }

  switch (transaction.partition_type) {
    case kDifFlashCtrlPartitionTypeData:
      control_reg = bitfield_bit32_write(
          control_reg, FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, false);
      break;
    case kDifFlashCtrlPartitionTypeInfo:
      control_reg =
          bitfield_field32_write(control_reg, FLASH_CTRL_CONTROL_INFO_SEL_FIELD,
                                 transaction.partition_id);
      control_reg = bitfield_bit32_write(
          control_reg, FLASH_CTRL_CONTROL_PARTITION_SEL_BIT, true);
      break;
    default:
      return kDifBadArg;
  }

  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_CONTROL_REG_OFFSET,
                      control_reg);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_ADDR_REG_OFFSET,
                      transaction.byte_address);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_CONTROL_REG_OFFSET,
                      control_reg | (1u << FLASH_CTRL_CONTROL_START_BIT));
  if (transaction.op == kDifFlashCtrlOpPageErase ||
      transaction.op == kDifFlashCtrlOpBankErase) {
    // Erase operations don't use the FIFO
    handle->words_remaining = 0;
  } else {
    handle->words_remaining = transaction.word_count;
  }
  handle->transaction_pending = true;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_start(dif_flash_ctrl_state_t *handle,
                                  dif_flash_ctrl_transaction_t transaction) {
  if (handle == NULL) {
    return kDifBadArg;
  }

  if (transaction.partition_type == kDifFlashCtrlPartitionTypeInfo &&
      transaction.partition_id >= FLASH_CTRL_NUM_INFO_TYPES) {
    return kDifBadArg;
  }

  const uint32_t max_word_count = FLASH_CTRL_CONTROL_NUM_MASK;
  if ((transaction.op != kDifFlashCtrlOpPageErase) &&
      (transaction.op != kDifFlashCtrlOpBankErase)) {
    if (transaction.word_count - 1 > max_word_count ||
        transaction.word_count == 0) {
      return kDifBadArg;
    }
  }

  if (handle->transaction_pending) {
    return kDifUnavailable;
  }

  // Disallow starting a new transaction if the FIFOs haven't been emptied yet.
  dif_flash_ctrl_status_t status;
  dif_result_t result = dif_flash_ctrl_get_status(handle, &status);
  if (result != kDifOk) {
    return result;
  }
  if (!status.read_fifo_empty || !status.prog_fifo_empty) {
    return kDifIpFifoFull;
  }

  return dif_flash_ctrl_start_unsafe(handle, transaction);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_suspend_erase(dif_flash_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      bitfield_bit32_write(0, FLASH_CTRL_ERASE_SUSPEND_REQ_BIT, true);
  mmio_region_write32(handle->dev.base_addr,
                      FLASH_CTRL_ERASE_SUSPEND_REG_OFFSET, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_erase_suspend_status(
    dif_flash_ctrl_state_t *handle, bool *request_pending_out) {
  if (handle == NULL || request_pending_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_ERASE_SUSPEND_REG_OFFSET);
  *request_pending_out =
      bitfield_bit32_read(reg, FLASH_CTRL_ERASE_SUSPEND_REQ_BIT);
  return kDifOk;
}

// TODO(awill): Function to report the maximum FIFO size?

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_prog_fifo_push_unsafe(
    dif_flash_ctrl_state_t *handle, uint32_t word_count, const uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  uint32_t written = 0;
  while (written < word_count) {
    mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_PROG_FIFO_REG_OFFSET,
                        data[written]);
    ++written;
  }
  handle->words_remaining -= written;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_prog_fifo_push(dif_flash_ctrl_state_t *handle,
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
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_CONTROL_REG_OFFSET);
  const uint32_t op =
      bitfield_field32_read(control_reg, FLASH_CTRL_CONTROL_OP_FIELD);
  if (op != FLASH_CTRL_CONTROL_OP_VALUE_PROG) {
    return kDifError;
  }
  return dif_flash_ctrl_prog_fifo_push_unsafe(handle, word_count, data);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_read_fifo_pop_unsafe(dif_flash_ctrl_state_t *handle,
                                                 uint32_t word_count,
                                                 uint32_t *data) {
  if (handle == NULL || data == NULL) {
    return kDifBadArg;
  }
  uint32_t read = 0;
  while (read < word_count) {
    data[read] = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_RD_FIFO_REG_OFFSET);
    ++read;
  }
  handle->words_remaining -= read;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_read_fifo_pop(dif_flash_ctrl_state_t *handle,
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
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_CONTROL_REG_OFFSET);
  const uint32_t op =
      bitfield_field32_read(control_reg, FLASH_CTRL_CONTROL_OP_FIELD);
  if (op != FLASH_CTRL_CONTROL_OP_VALUE_READ) {
    return kDifError;
  }
  return dif_flash_ctrl_read_fifo_pop_unsafe(handle, word_count, data);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_error_codes(
    const dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_error_t *error_code_out) {
  if (handle == NULL || error_code_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t code_reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_ERR_CODE_REG_OFFSET);
  dif_flash_ctrl_error_codes_t codes = {
      .memory_properties_error =
          bitfield_bit32_read(code_reg, FLASH_CTRL_ERR_CODE_MP_ERR_BIT),
      .read_error =
          bitfield_bit32_read(code_reg, FLASH_CTRL_ERR_CODE_RD_ERR_BIT),
      .prog_window_error =
          bitfield_bit32_read(code_reg, FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT),
      .prog_type_error =
          bitfield_bit32_read(code_reg, FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT),
      .shadow_register_error =
          bitfield_bit32_read(code_reg, FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT),
  };

  const uint32_t address_reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_ERR_ADDR_REG_OFFSET);
  dif_flash_ctrl_error_t error_code = {
      .address = address_reg,
      .codes = codes,
  };
  *error_code_out = error_code;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_clear_error_codes(
    dif_flash_ctrl_state_t *handle, dif_flash_ctrl_error_codes_t codes) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t code_reg = 0;
  code_reg = bitfield_bit32_write(code_reg, FLASH_CTRL_ERR_CODE_MP_ERR_BIT,
                                  codes.memory_properties_error);
  code_reg = bitfield_bit32_write(code_reg, FLASH_CTRL_ERR_CODE_RD_ERR_BIT,
                                  codes.read_error);
  code_reg = bitfield_bit32_write(
      code_reg, FLASH_CTRL_ERR_CODE_PROG_WIN_ERR_BIT, codes.prog_window_error);
  code_reg = bitfield_bit32_write(
      code_reg, FLASH_CTRL_ERR_CODE_PROG_TYPE_ERR_BIT, codes.prog_type_error);
  code_reg = bitfield_bit32_write(code_reg, FLASH_CTRL_ERR_CODE_UPDATE_ERR_BIT,
                                  codes.shadow_register_error);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_ERR_CODE_REG_OFFSET,
                      code_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_end(dif_flash_ctrl_state_t *handle,
                                dif_flash_ctrl_output_t *out) {
  if (handle == NULL || out == NULL) {
    return kDifBadArg;
  }
  if (!handle->transaction_pending) {
    return kDifError;
  }
  uint32_t status_reg = mmio_region_read32(handle->dev.base_addr,
                                           FLASH_CTRL_OP_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(status_reg, FLASH_CTRL_OP_STATUS_DONE_BIT)) {
    return kDifUnavailable;
  }
  if (handle->words_remaining != 0) {
    return kDifIpFifoFull;
  }
  out->operation_done =
      bitfield_bit32_read(status_reg, FLASH_CTRL_OP_STATUS_DONE_BIT);
  out->operation_error =
      bitfield_bit32_read(status_reg, FLASH_CTRL_OP_STATUS_ERR_BIT);
  // Clear the operation status
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_OP_STATUS_REG_OFFSET,
                      0);
  handle->transaction_pending = false;
  return dif_flash_ctrl_get_error_codes(handle, &out->error_code);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_data_region_enablement(
    dif_flash_ctrl_state_t *handle, uint32_t region, dif_toggle_t enable) {
  if (handle == NULL || region >= FLASH_CTRL_PARAM_NUM_REGIONS) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  switch (enable) {
    case kDifToggleEnabled:
      mp_reg = bitfield_field32_write(
          mp_reg, FLASH_CTRL_MP_REGION_CFG_0_EN_0_FIELD, kMultiBitBool4True);
      break;
    case kDifToggleDisabled:
      mp_reg = bitfield_field32_write(
          mp_reg, FLASH_CTRL_MP_REGION_CFG_0_EN_0_FIELD, kMultiBitBool4False);
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, mp_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_data_region_enablement(
    const dif_flash_ctrl_state_t *handle, uint32_t region,
    dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL ||
      region >= FLASH_CTRL_PARAM_NUM_REGIONS) {
    return kDifBadArg;
  }
  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  if (bitfield_field32_read(mp_reg, FLASH_CTRL_MP_REGION_CFG_0_EN_0_FIELD) ==
      kMultiBitBool4True) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_info_region_enablement(
    dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region,
    dif_toggle_t enable) {
  if (handle == NULL || region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }
  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  switch (enable) {
    case kDifToggleEnabled:
      mp_reg = bitfield_field32_write(
          mp_reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_EN_0_FIELD,
          kMultiBitBool4True);
      break;
    case kDifToggleDisabled:
      mp_reg = bitfield_field32_write(
          mp_reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_EN_0_FIELD,
          kMultiBitBool4False);
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, mp_reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_info_region_enablement(
    const dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region,
    dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL ||
      region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }
  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t mp_reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  if (bitfield_field32_read(mp_reg, FLASH_CTRL_MP_REGION_CFG_0_EN_0_FIELD) ==
      kMultiBitBool4True) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_default_region_properties(
    dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_region_properties_t properties) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_RD_EN_FIELD,
                               properties.rd_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_PROG_EN_FIELD,
                               properties.prog_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_ERASE_EN_FIELD,
                               properties.erase_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD,
                               properties.scramble_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_ECC_EN_FIELD,
                               properties.ecc_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_DEFAULT_REGION_HE_EN_FIELD,
                               properties.high_endurance_en);
  mmio_region_write32(handle->dev.base_addr,
                      FLASH_CTRL_DEFAULT_REGION_REG_OFFSET, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_default_region_properties(
    const dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_region_properties_t *properties_out) {
  if (handle == NULL || properties_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                          FLASH_CTRL_DEFAULT_REGION_REG_OFFSET);
  dif_flash_ctrl_region_properties_t properties = {
      .rd_en =
          bitfield_field32_read(reg, FLASH_CTRL_DEFAULT_REGION_RD_EN_FIELD),
      .prog_en =
          bitfield_field32_read(reg, FLASH_CTRL_DEFAULT_REGION_PROG_EN_FIELD),
      .erase_en =
          bitfield_field32_read(reg, FLASH_CTRL_DEFAULT_REGION_ERASE_EN_FIELD),
      .scramble_en = bitfield_field32_read(
          reg, FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD),
      .ecc_en =
          bitfield_field32_read(reg, FLASH_CTRL_DEFAULT_REGION_ECC_EN_FIELD),
      .high_endurance_en =
          bitfield_field32_read(reg, FLASH_CTRL_DEFAULT_REGION_HE_EN_FIELD),
  };
  *properties_out = properties;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_data_region_properties(
    dif_flash_ctrl_state_t *handle, uint32_t region,
    dif_flash_ctrl_data_region_properties_t config) {
  const uint32_t page_limit =
      FLASH_CTRL_PARAM_REG_NUM_BANKS * FLASH_CTRL_PARAM_REG_PAGES_PER_BANK;
  if (handle == NULL || region >= FLASH_CTRL_PARAM_NUM_REGIONS ||
      config.base + config.size > page_limit) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_RD_EN_0_FIELD,
                               config.properties.rd_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_PROG_EN_0_FIELD,
                               config.properties.prog_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_ERASE_EN_0_FIELD,
                               config.properties.erase_en);
  reg = bitfield_field32_write(reg,
                               FLASH_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_FIELD,
                               config.properties.scramble_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_ECC_EN_0_FIELD,
                               config.properties.ecc_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_HE_EN_0_FIELD,
                               config.properties.high_endurance_en);

  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);

  // size and base are stored in different registers
  mp_reg_offset = get_data_region_reg_offset(region);

  reg = bitfield_field32_write(0, FLASH_CTRL_MP_REGION_0_BASE_0_FIELD,
                               config.base);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_0_SIZE_0_FIELD,
                               config.size);
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_data_region_properties(
    const dif_flash_ctrl_state_t *handle, uint32_t region,
    dif_flash_ctrl_data_region_properties_t *config_out) {
  if (handle == NULL || config_out == NULL ||
      region >= FLASH_CTRL_PARAM_NUM_REGIONS) {
    return kDifBadArg;
  }

  ptrdiff_t mp_reg_offset = get_data_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  dif_flash_ctrl_data_region_properties_t config;
  config.properties.rd_en =
      bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_CFG_0_RD_EN_0_FIELD);
  config.properties.prog_en =
      bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_CFG_0_PROG_EN_0_FIELD);
  config.properties.erase_en =
      bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_CFG_0_ERASE_EN_0_FIELD);
  config.properties.scramble_en = bitfield_field32_read(
      reg, FLASH_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_FIELD);
  config.properties.ecc_en =
      bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_CFG_0_ECC_EN_0_FIELD);
  config.properties.high_endurance_en =
      bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_CFG_0_HE_EN_0_FIELD);

  mp_reg_offset = get_data_region_reg_offset(region);
  reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  config.base = bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_0_BASE_0_FIELD);
  config.size = bitfield_field32_read(reg, FLASH_CTRL_MP_REGION_0_SIZE_0_FIELD);
  *config_out = config;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_info_region_properties(
    dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region,
    dif_flash_ctrl_region_properties_t properties) {
  if (handle == NULL || region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifLocked;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_RD_EN_0_FIELD,
                               properties.rd_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_PROG_EN_0_FIELD,
                               properties.prog_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_ERASE_EN_0_FIELD,
                               properties.erase_en);
  reg = bitfield_field32_write(reg,
                               FLASH_CTRL_MP_REGION_CFG_0_SCRAMBLE_EN_0_FIELD,
                               properties.scramble_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_ECC_EN_0_FIELD,
                               properties.ecc_en);
  reg = bitfield_field32_write(reg, FLASH_CTRL_MP_REGION_CFG_0_HE_EN_0_FIELD,
                               properties.high_endurance_en);
  mmio_region_write32(handle->dev.base_addr, mp_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_info_region_properties(
    const dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region,
    dif_flash_ctrl_region_properties_t *properties_out) {
  if (handle == NULL || properties_out == NULL ||
      region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }

  ptrdiff_t mp_reg_offset = get_info_region_mp_reg_offset(region);
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr, mp_reg_offset);
  dif_flash_ctrl_region_properties_t properties;
  properties.rd_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_RD_EN_0_FIELD);
  properties.prog_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_PROG_EN_0_FIELD);
  properties.erase_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_ERASE_EN_0_FIELD);
  properties.scramble_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_SCRAMBLE_EN_0_FIELD);
  properties.ecc_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_ECC_EN_0_FIELD);
  properties.high_endurance_en = bitfield_field32_read(
      reg, FLASH_CTRL_BANK0_INFO0_PAGE_CFG_0_HE_EN_0_FIELD);
  *properties_out = properties;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_lock_data_region_properties(
    dif_flash_ctrl_state_t *handle, uint32_t region) {
  if (handle == NULL || region >= FLASH_CTRL_PARAM_NUM_REGIONS) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_data_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifOk;
  }

  ptrdiff_t lock_reg_offset = get_data_region_lock_reg_offset(region);
  uint32_t reg = bitfield_bit32_write(
      0, FLASH_CTRL_REGION_CFG_REGWEN_0_REGION_0_BIT, false);
  mmio_region_write32(handle->dev.base_addr, lock_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_lock_info_region_properties(
    dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region) {
  if (handle == NULL || region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_info_region_is_locked(handle, region, &locked));
  if (locked) {
    return kDifOk;
  }

  ptrdiff_t lock_reg_offset = get_info_region_lock_reg_offset(region);
  uint32_t reg = bitfield_bit32_write(
      0, FLASH_CTRL_BANK0_INFO0_REGWEN_0_REGION_0_BIT, false);
  mmio_region_write32(handle->dev.base_addr, lock_reg_offset, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_data_region_is_locked(
    const dif_flash_ctrl_state_t *handle, uint32_t region, bool *locked_out) {
  if (handle == NULL || locked_out == NULL ||
      region >= FLASH_CTRL_PARAM_NUM_REGIONS) {
    return kDifBadArg;
  }
  ptrdiff_t lock_reg_offset = get_data_region_lock_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, lock_reg_offset);
  *locked_out =
      !bitfield_bit32_read(reg, FLASH_CTRL_REGION_CFG_REGWEN_0_REGION_0_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_info_region_is_locked(
    const dif_flash_ctrl_state_t *handle, dif_flash_ctrl_info_region_t region,
    bool *locked_out) {
  if (handle == NULL || locked_out == NULL ||
      region.bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS ||
      region.partition_id >= FLASH_CTRL_NUM_INFO_TYPES ||
      region.page > kNumInfoPagesPerBank[region.partition_id]) {
    return kDifBadArg;
  }

  ptrdiff_t lock_reg_offset = get_info_region_lock_reg_offset(region);
  uint32_t reg = mmio_region_read32(handle->dev.base_addr, lock_reg_offset);
  *locked_out =
      !bitfield_bit32_read(reg, FLASH_CTRL_BANK0_INFO0_REGWEN_0_REGION_0_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_bank_erase_enablement(
    dif_flash_ctrl_state_t *handle, uint32_t bank, dif_toggle_t enable) {
  if (handle == NULL || bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_bank_configuration_is_locked(handle, &locked));
  if (locked) {
    return kDifLocked;
  }

  bitfield_bit32_index_t index = bank;
  uint32_t value = mmio_region_read32(
      handle->dev.base_addr, FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET);
  switch (enable) {
    case kDifToggleEnabled:
      value = bitfield_bit32_write(value, index, true);
      break;
    case kDifToggleDisabled:
      value = bitfield_bit32_write(value, index, false);
      break;
    default:
      return kDifBadArg;
  }
  mmio_region_write32_shadowed(
      handle->dev.base_addr, FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET, value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_bank_erase_enablement(
    const dif_flash_ctrl_state_t *handle, uint32_t bank,
    dif_toggle_t *enabled_out) {
  if (handle == NULL || enabled_out == NULL ||
      bank >= FLASH_CTRL_PARAM_REG_NUM_BANKS) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_MP_BANK_CFG_SHADOWED_REG_OFFSET);
  bitfield_bit32_index_t index = bank;
  bool enabled = bitfield_bit32_read(reg, index);
  if (enabled) {
    *enabled_out = kDifToggleEnabled;
  } else {
    *enabled_out = kDifToggleDisabled;
  }
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_lock_bank_configuration(
    dif_flash_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }

  bool locked;
  DIF_RETURN_IF_ERROR(
      dif_flash_ctrl_bank_configuration_is_locked(handle, &locked));
  if (locked) {
    return kDifLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, FLASH_CTRL_BANK_CFG_REGWEN_BANK_BIT, false);
  mmio_region_write32(handle->dev.base_addr,
                      FLASH_CTRL_BANK_CFG_REGWEN_REG_OFFSET, reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_bank_configuration_is_locked(
    const dif_flash_ctrl_state_t *handle, bool *locked_out) {
  if (handle == NULL || locked_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg = mmio_region_read32(
      handle->dev.base_addr, FLASH_CTRL_BANK_CFG_REGWEN_REG_OFFSET);
  *locked_out = !bitfield_bit32_read(reg, FLASH_CTRL_BANK_CFG_REGWEN_BANK_BIT);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_prog_fifo_watermark(
    dif_flash_ctrl_state_t *handle, uint32_t level) {
  if (handle == NULL || level > FLASH_CTRL_FIFO_LVL_PROG_MASK) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  reg = bitfield_field32_write(reg, FLASH_CTRL_FIFO_LVL_PROG_FIELD, level);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_read_fifo_watermark(
    dif_flash_ctrl_state_t *handle, uint32_t level) {
  if (handle == NULL || level > FLASH_CTRL_FIFO_LVL_RD_MASK) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  reg = bitfield_field32_write(reg, FLASH_CTRL_FIFO_LVL_RD_FIELD, level);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_fifo_watermarks(
    const dif_flash_ctrl_state_t *handle, uint32_t *prog_out,
    uint32_t *read_out) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_FIFO_LVL_REG_OFFSET);
  if (prog_out != NULL) {
    *prog_out = bitfield_field32_read(reg, FLASH_CTRL_FIFO_LVL_PROG_FIELD);
  }
  if (read_out != NULL) {
    *read_out = bitfield_field32_read(reg, FLASH_CTRL_FIFO_LVL_RD_FIELD);
  }
  return kDifOk;
}

// TODO: Allow splitting up turning the reset on and off?
OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_reset_fifos(dif_flash_ctrl_state_t *handle) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = bitfield_bit32_write(0, FLASH_CTRL_FIFO_RST_EN_BIT, true);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_FIFO_RST_REG_OFFSET,
                      reg);
  reg = bitfield_bit32_write(0, FLASH_CTRL_FIFO_RST_EN_BIT, false);
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_FIFO_RST_REG_OFFSET,
                      reg);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_faults(const dif_flash_ctrl_state_t *handle,
                                       dif_flash_ctrl_faults_t *faults_out) {
  if (handle == NULL || faults_out == NULL) {
    return kDifBadArg;
  }
  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_FAULT_STATUS_REG_OFFSET);
  dif_flash_ctrl_faults_t faults;
  faults.memory_properties_error =
      bitfield_bit32_read(reg, FLASH_CTRL_FAULT_STATUS_MP_ERR_BIT);
  faults.read_error =
      bitfield_bit32_read(reg, FLASH_CTRL_FAULT_STATUS_RD_ERR_BIT);
  faults.prog_window_error =
      bitfield_bit32_read(reg, FLASH_CTRL_FAULT_STATUS_PROG_WIN_ERR_BIT);
  faults.prog_type_error =
      bitfield_bit32_read(reg, FLASH_CTRL_FAULT_STATUS_PROG_TYPE_ERR_BIT);
  faults.host_gnt_error =
      bitfield_bit32_read(reg, FLASH_CTRL_FAULT_STATUS_HOST_GNT_ERR_BIT);
  reg = mmio_region_read32(handle->dev.base_addr,
                           FLASH_CTRL_STD_FAULT_STATUS_REG_OFFSET);
  faults.register_integrity_error =
      bitfield_bit32_read(reg, FLASH_CTRL_STD_FAULT_STATUS_REG_INTG_ERR_BIT);
  faults.phy_integrity_error =
      bitfield_bit32_read(reg, FLASH_CTRL_STD_FAULT_STATUS_PROG_INTG_ERR_BIT);
  faults.lifecycle_manager_error =
      bitfield_bit32_read(reg, FLASH_CTRL_STD_FAULT_STATUS_LCMGR_ERR_BIT);
  faults.shadow_storage_error =
      bitfield_bit32_read(reg, FLASH_CTRL_STD_FAULT_STATUS_STORAGE_ERR_BIT);
  *faults_out = faults;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_ecc_errors(
    const dif_flash_ctrl_state_t *handle, uint32_t bank,
    dif_flash_ctrl_ecc_errors_t *errors_out) {
  if (handle == NULL || errors_out == NULL ||
      bank > FLASH_CTRL_PARAM_REG_NUM_BANKS) {
    return kDifBadArg;
  }
  bitfield_field32_t error_count_field;
  ptrdiff_t last_addr_reg_offset;
#if FLASH_CTRL_PARAM_REG_NUM_BANKS > 2
#error "Revise this function to handle more banks."
#endif
  if (bank == 0) {
    error_count_field =
        FLASH_CTRL_ECC_SINGLE_ERR_CNT_ECC_SINGLE_ERR_CNT_0_FIELD;
    last_addr_reg_offset = FLASH_CTRL_ECC_SINGLE_ERR_ADDR_0_REG_OFFSET;
  } else {
    error_count_field =
        FLASH_CTRL_ECC_SINGLE_ERR_CNT_ECC_SINGLE_ERR_CNT_1_FIELD;
    last_addr_reg_offset = FLASH_CTRL_ECC_SINGLE_ERR_ADDR_1_REG_OFFSET;
  }

  uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                    FLASH_CTRL_ECC_SINGLE_ERR_CNT_REG_OFFSET);
  errors_out->single_bit_error_count =
      bitfield_field32_read(reg, error_count_field);
  errors_out->last_error_address =
      mmio_region_read32(handle->dev.base_addr, last_addr_reg_offset);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_phy_status(
    const dif_flash_ctrl_state_t *handle,
    dif_flash_ctrl_phy_status_t *status_out) {
  if (handle == NULL || status_out == NULL) {
    return kDifBadArg;
  }
  const uint32_t reg = mmio_region_read32(handle->dev.base_addr,
                                          FLASH_CTRL_PHY_STATUS_REG_OFFSET);
  dif_flash_ctrl_phy_status_t status = {
      .phy_init_wip =
          bitfield_bit32_read(reg, FLASH_CTRL_PHY_STATUS_INIT_WIP_BIT),
      .prog_normal_available =
          bitfield_bit32_read(reg, FLASH_CTRL_PHY_STATUS_PROG_NORMAL_AVAIL_BIT),
      .prog_repair_available =
          bitfield_bit32_read(reg, FLASH_CTRL_PHY_STATUS_PROG_REPAIR_AVAIL_BIT),
  };
  *status_out = status;
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_set_scratch(dif_flash_ctrl_state_t *handle,
                                        uint32_t value) {
  if (handle == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(handle->dev.base_addr, FLASH_CTRL_SCRATCH_REG_OFFSET,
                      value);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_flash_ctrl_get_scratch(const dif_flash_ctrl_state_t *handle,
                                        uint32_t *value_out) {
  if (handle == NULL || value_out == NULL) {
    return kDifBadArg;
  }
  *value_out =
      mmio_region_read32(handle->dev.base_addr, FLASH_CTRL_SCRATCH_REG_OFFSET);
  return kDifOk;
}
