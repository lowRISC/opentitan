// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_keymgr.h"

#include <assert.h>

#include "keymgr_regs.h"  // Generated.

/**
 * Address spaces of SW_BINDING_N, SALT_N, SW_SHARE0_OUTPUT_N, and
 * SW_SHARE1_OUTPUT_N registers must be contiguous to be able to use
 * `mmio_region_memcpy_to/from_mmio32()`.
 */
static_assert(KEYMGR_SW_BINDING_1_REG_OFFSET ==
                  KEYMGR_SW_BINDING_0_REG_OFFSET + 4,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_SW_BINDING_2_REG_OFFSET ==
                  KEYMGR_SW_BINDING_0_REG_OFFSET + 8,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_SW_BINDING_3_REG_OFFSET ==
                  KEYMGR_SW_BINDING_0_REG_OFFSET + 12,
              "SW_BINDING_N registers must be contiguous.");
// TODO: Uncomment when lowRISC/opentitan#5194 is completed.
// TODO: Consider defining a macro once all assertions are enabled.
// static_assert(KEYMGR_SW_BINDING_4_REG_OFFSET ==
//                   KEYMGR_SW_BINDING_0_REG_OFFSET + 16,
//               "SW_BINDING_N registers must be contiguous.");
// static_assert(KEYMGR_SW_BINDING_5_REG_OFFSET ==
//                   KEYMGR_SW_BINDING_0_REG_OFFSET + 20,
//               "SW_BINDING_N registers must be contiguous.");
// static_assert(KEYMGR_SW_BINDING_6_REG_OFFSET ==
//                   KEYMGR_SW_BINDING_0_REG_OFFSET + 24,
//               "SW_BINDING_N registers must be contiguous.");
// static_assert(KEYMGR_SW_BINDING_7_REG_OFFSET ==
//                   KEYMGR_SW_BINDING_0_REG_OFFSET + 28,
//               "SW_BINDING_N registers must be contiguous.");

static_assert(KEYMGR_SALT_1_REG_OFFSET == KEYMGR_SALT_0_REG_OFFSET + 4,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_SALT_2_REG_OFFSET == KEYMGR_SALT_0_REG_OFFSET + 8,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_SALT_3_REG_OFFSET == KEYMGR_SALT_0_REG_OFFSET + 12,
              "SALT_N registers must be contiguous.");
// TODO: Uncomment when lowRISC/opentitan#5194 is completed.
// static_assert(KEYMGR_SALT_4_REG_OFFSET ==
//                   KEYMGR_SALT_0_REG_OFFSET + 16,
//               "SALT_N registers must be contiguous.");
// static_assert(KEYMGR_SALT_5_REG_OFFSET ==
//                   KEYMGR_SALT_0_REG_OFFSET + 20,
//               "SALT_N registers must be contiguous.");
// static_assert(KEYMGR_SALT_6_REG_OFFSET ==
//                   KEYMGR_SALT_0_REG_OFFSET + 24,
//               "SALT_N registers must be contiguous.");
// static_assert(KEYMGR_SALT_7_REG_OFFSET ==
//                   KEYMGR_SALT_0_REG_OFFSET + 28,
//               "SALT_N registers must be contiguous.");

static_assert(KEYMGR_SW_SHARE0_OUTPUT_1_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 4,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_2_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 8,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_3_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 12,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_4_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 16,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_5_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 20,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_6_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 24,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE0_OUTPUT_7_REG_OFFSET ==
                  KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET + 28,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");

static_assert(KEYMGR_SW_SHARE1_OUTPUT_1_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 4,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_2_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 8,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_3_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 12,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_4_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 16,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_5_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 20,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_6_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 24,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_SW_SHARE1_OUTPUT_7_REG_OFFSET ==
                  KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET + 28,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");

/**
 * Error code constants of `dif_keymgr_status_code_t` are masks for the bits of
 * ERR_CODE register shifted left by 1.
 */
static_assert(kDifKeymgrStatusCodeInvalidOperation >> 1 ==
                  1 << KEYMGR_ERR_CODE_INVALID_OP_BIT,
              "Layout of ERR_CODE register changed.");
static_assert(kDifKeymgrStatusCodeInvalidKmacCommand >> 1 ==
                  1 << KEYMGR_ERR_CODE_INVALID_CMD_BIT,
              "Layout of ERR_CODE register changed.");
static_assert(kDifKeymgrStatusCodeInvalidKmacInput >> 1 ==
                  1 << KEYMGR_ERR_CODE_INVALID_KMAC_INPUT_BIT,
              "Layout of ERR_CODE register changed.");
static_assert(kDifKeymgrStatusCodeInvalidKmacOutput >> 1 ==
                  1 << KEYMGR_ERR_CODE_INVALID_KMAC_DATA_BIT,
              "Layout of ERR_CODE register changed.");

/**
 * Checks if the key manager is ready for a new operation, i.e. it is idle and
 * the CONFIG register is unlocked.
 */
DIF_WARN_UNUSED_RESULT
static bool is_ready(const dif_keymgr_t *keymgr) {
  // Keymgr must be idle and the CONTROL register must be writable.
  uint32_t reg_op_status =
      mmio_region_read32(keymgr->params.base_addr, KEYMGR_OP_STATUS_REG_OFFSET);
  if (bitfield_field32_read(reg_op_status, KEYMGR_OP_STATUS_STATUS_FIELD) !=
      KEYMGR_OP_STATUS_STATUS_VALUE_IDLE) {
    return false;
  }
  uint32_t reg_cfg_regwen = mmio_region_read32(keymgr->params.base_addr,
                                               KEYMGR_CFG_REGWEN_REG_OFFSET);
  return bitfield_bit32_read(reg_cfg_regwen, KEYMGR_CFG_REGWEN_EN_BIT);
}

/**
 * Max key version register information for a state transition.
 */
typedef struct max_key_version_reg_info {
  /**
   * Whether max key version must be set for this transition or not.
   */
  bool is_required;
  /**
   * Max key version register offset to use.
   */
  uint32_t reg_offset;
  /**
   * Write-enable register offset to use.
   */
  uint32_t wen_reg_offset;
  /**
   * Write-enable bit index.
   */
  bitfield_bit32_index_t wen_bit_index;
} max_key_version_reg_info_t;

/**
 * Returns max key version register information for transitioning from a state.
 */
DIF_WARN_UNUSED_RESULT
static bool get_max_key_version_reg_info_for_next_state(
    uint32_t cur_state, max_key_version_reg_info_t *reg_info) {
  switch (cur_state) {
    case KEYMGR_WORKING_STATE_STATE_VALUE_INIT:
      *reg_info = (max_key_version_reg_info_t){
          .is_required = true,
          .reg_offset = KEYMGR_MAX_CREATOR_KEY_VER_REG_OFFSET,
          .wen_reg_offset = KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET,
          .wen_bit_index = KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_EN_BIT,
      };
      return true;
    case KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY:
      *reg_info = (max_key_version_reg_info_t){
          .is_required = true,
          .reg_offset = KEYMGR_MAX_OWNER_INT_KEY_VER_REG_OFFSET,
          .wen_reg_offset = KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_OFFSET,
          .wen_bit_index = KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_EN_BIT,
      };
      return true;
    case KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY:
      *reg_info = (max_key_version_reg_info_t){
          .is_required = true,
          .reg_offset = KEYMGR_MAX_OWNER_KEY_VER_REG_OFFSET,
          .wen_reg_offset = KEYMGR_MAX_OWNER_KEY_VER_REGWEN_REG_OFFSET,
          .wen_bit_index = KEYMGR_MAX_OWNER_KEY_VER_REGWEN_EN_BIT,
      };
      return true;
    case KEYMGR_WORKING_STATE_STATE_VALUE_RESET:
    case KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY:
    case KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED:
    case KEYMGR_WORKING_STATE_STATE_VALUE_INVALID:
      *reg_info = (max_key_version_reg_info_t){
          .is_required = false,
      };
      return true;
    default:
      return false;
  }
}

/**
 * Parameters for starting a key manager operation.
 *
 * Values of the members must be the actual values that will be written to the
 * CONTROL register.
 */
typedef struct start_operation_params {
  /**
   * Destination for this operation.
   */
  uint32_t dest;
  /**
   * Operation to start.
   */
  uint32_t op;
} start_operation_params_t;

/**
 * Starts a key manager operation.
 */
static void start_operation(const dif_keymgr_t *keymgr,
                            start_operation_params_t params) {
  uint32_t reg_control =
      bitfield_field32_write(0, KEYMGR_CONTROL_DEST_SEL_FIELD, params.dest);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_CONTROL_OPERATION_FIELD, params.op);
  reg_control =
      bitfield_bit32_write(reg_control, KEYMGR_CONTROL_START_BIT, true);
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_CONTROL_REG_OFFSET,
                      reg_control);
}

/**
 * Returns the bit index for a given IRQ.
 */
DIF_WARN_UNUSED_RESULT
static bool get_irq_bit_index(dif_keymgr_irq_t irq,
                              bitfield_bit32_index_t *bit_index) {
  switch (irq) {
    case kDifKeymgrIrqDone:
      *bit_index = KEYMGR_INTR_COMMON_OP_DONE_BIT;
      return true;
    default:
      return false;
  }
}

/**
 * Checks if a value is a valid `dif_keymgr_toggle_t` and converts it to `bool`.
 */
DIF_WARN_UNUSED_RESULT
static bool toggle_to_bool(dif_keymgr_toggle_t val, bool *val_bool) {
  switch (val) {
    case kDifKeymgrToggleEnabled:
      *val_bool = true;
      break;
    case kDifKeymgrToggleDisabled:
      *val_bool = false;
      break;
    default:
      return false;
  }
  return true;
}

/**
 * Converts a `bool` to `dif_keymgr_toggle_t`.
 */
static dif_keymgr_toggle_t bool_to_toggle(bool val) {
  return val ? kDifKeymgrToggleEnabled : kDifKeymgrToggleDisabled;
}

dif_keymgr_result_t dif_keymgr_init(dif_keymgr_params_t params,
                                    dif_keymgr_t *keymgr) {
  if (keymgr == NULL) {
    return kDifKeymgrBadArg;
  }

  *keymgr = (dif_keymgr_t){.params = params};

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_configure(const dif_keymgr_t *keymgr,
                                         dif_keymgr_config_t config) {
  if (keymgr == NULL) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = bitfield_field32_write(0, KEYMGR_RESEED_INTERVAL_VAL_FIELD,
                                            config.entropy_reseed_interval);
  mmio_region_write32(keymgr->params.base_addr,
                      KEYMGR_RESEED_INTERVAL_REG_OFFSET, reg_val);

  return kDifKeymgrOk;
}

dif_keymgr_lockable_result_t dif_keymgr_advance_state(
    const dif_keymgr_t *keymgr, const dif_keymgr_state_params_t *params) {
  if (keymgr == NULL) {
    return kDifKeymgrLockableBadArg;
  }

  if (!is_ready(keymgr)) {
    return kDifKeymgrLockableLocked;
  }

  // Get current state and determine if we need to set the max key version and
  // sw binding value.
  max_key_version_reg_info_t max_key_ver_reg_info;
  uint32_t reg_working_state = mmio_region_read32(
      keymgr->params.base_addr, KEYMGR_WORKING_STATE_REG_OFFSET);
  if (!get_max_key_version_reg_info_for_next_state(
          (bitfield_field32_read(reg_working_state,
                                 KEYMGR_WORKING_STATE_STATE_FIELD)),
          &max_key_ver_reg_info)) {
    return kDifKeymgrLockableError;
  }

  // Set the binding value and max key version if keymgr is going to
  // transition to an operational state.
  if (max_key_ver_reg_info.is_required) {
    if (params == NULL) {
      return kDifKeymgrLockableBadArg;
    }

    // Check if SW_BINDING_N registers are locked
    uint32_t reg_sw_binding_wen = mmio_region_read32(
        keymgr->params.base_addr, KEYMGR_SW_BINDING_REGWEN_REG_OFFSET);
    if (!bitfield_bit32_read(reg_sw_binding_wen,
                             KEYMGR_SW_BINDING_REGWEN_EN_BIT)) {
      return kDifKeymgrLockableLocked;
    }

    // Check if MAX_*_KEY_VER register is locked.
    uint32_t reg_max_key_ver_wen = mmio_region_read32(
        keymgr->params.base_addr, max_key_ver_reg_info.wen_reg_offset);
    if (!bitfield_bit32_read(reg_max_key_ver_wen,
                             max_key_ver_reg_info.wen_bit_index)) {
      return kDifKeymgrLockableLocked;
    }

    // Write and lock (rw0c) the software binding value. This register is
    // unlocked by hardware upon a successful state transition.
    mmio_region_memcpy_to_mmio32(
        keymgr->params.base_addr, KEYMGR_SW_BINDING_0_REG_OFFSET,
        params->binding_value, sizeof(params->binding_value));
    mmio_region_write32(keymgr->params.base_addr,
                        KEYMGR_SW_BINDING_REGWEN_REG_OFFSET, 0);

    // Write and lock (rw0c) the max key version.
    mmio_region_write32(keymgr->params.base_addr,
                        max_key_ver_reg_info.reg_offset,
                        params->max_key_version);
    mmio_region_write32(keymgr->params.base_addr,
                        max_key_ver_reg_info.wen_reg_offset, 0);
  } else if (params != NULL) {
    return kDifKeymgrLockableBadArg;
  }

  // Advance state.
  start_operation(keymgr, (start_operation_params_t){
                              .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
                              .op = KEYMGR_CONTROL_OPERATION_VALUE_ADVANCE,
                          });

  return kDifKeymgrLockableOk;
}

dif_keymgr_lockable_result_t dif_keymgr_disable(const dif_keymgr_t *keymgr) {
  if (keymgr == NULL) {
    return kDifKeymgrLockableBadArg;
  }

  if (!is_ready(keymgr)) {
    return kDifKeymgrLockableLocked;
  }

  // Disable key manager.
  start_operation(keymgr, (start_operation_params_t){
                              .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
                              .op = KEYMGR_CONTROL_OPERATION_VALUE_DISABLE,
                          });

  return kDifKeymgrLockableOk;
}

dif_keymgr_result_t dif_keymgr_get_status_codes(
    const dif_keymgr_t *keymgr, dif_keymgr_status_codes_t *status_codes) {
  if (keymgr == NULL || status_codes == NULL) {
    return kDifKeymgrBadArg;
  }

  // Read and clear OP_STATUS register (rw1c).
  uint32_t reg_op_status =
      mmio_region_read32(keymgr->params.base_addr, KEYMGR_OP_STATUS_REG_OFFSET);
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_OP_STATUS_REG_OFFSET,
                      reg_op_status);

  bool is_idle = false;
  bool has_error = false;
  switch (reg_op_status) {
    case KEYMGR_OP_STATUS_STATUS_VALUE_IDLE:
      is_idle = true;
      break;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      is_idle = true;
      break;
    case KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR:
      is_idle = true;
      has_error = true;
      break;
    case KEYMGR_OP_STATUS_STATUS_VALUE_WIP:
      break;
    default:
      return kDifKeymgrError;
  }

  // Bit 0 of `dif_keymgr_status_codes_t` indicates whether the key manager is
  // idle or not.
  *status_codes = bitfield_bit32_write(0, 0, is_idle);

  if (has_error) {
    // Read and clear ERR_CODE register (rw1c).
    uint32_t reg_err_code = mmio_region_read32(keymgr->params.base_addr,
                                               KEYMGR_ERR_CODE_REG_OFFSET);
    mmio_region_write32(keymgr->params.base_addr, KEYMGR_ERR_CODE_REG_OFFSET,
                        reg_err_code);
    // Error bits start from bit 1 in `dif_keymgr_status_codes_t`.
    // Note: The mask is hardcoded since it is not auto generated yet.
    const bitfield_field32_t kErrorBitfield = (bitfield_field32_t){
        .mask = 0xF,
        .index = 1,
    };
    if (reg_err_code > kErrorBitfield.mask || reg_err_code == 0) {
      return kDifKeymgrError;
    }
    *status_codes =
        bitfield_field32_write(*status_codes, kErrorBitfield, reg_err_code);
  }

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_get_state(const dif_keymgr_t *keymgr,
                                         dif_keymgr_state_t *state) {
  if (keymgr == NULL || state == NULL) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_state = mmio_region_read32(keymgr->params.base_addr,
                                          KEYMGR_WORKING_STATE_REG_OFFSET);

  switch (bitfield_field32_read(reg_state, KEYMGR_WORKING_STATE_STATE_FIELD)) {
    case KEYMGR_WORKING_STATE_STATE_VALUE_RESET:
      *state = kDifKeymgrStateReset;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_INIT:
      *state = kDifKeymgrStateInitialized;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY:
      *state = kDifKeymgrStateCreatorRootKey;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY:
      *state = kDifKeymgrStateOwnerIntermediateKey;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY:
      *state = kDifKeymgrStateOwnerRootKey;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED:
      *state = kDifKeymgrStateDisabled;
      return kDifKeymgrOk;
    case KEYMGR_WORKING_STATE_STATE_VALUE_INVALID:
      *state = kDifKeymgrStateInvalid;
      return kDifKeymgrOk;
    default:
      return kDifKeymgrError;
  }
}

dif_keymgr_lockable_result_t dif_keymgr_generate_identity_seed(
    const dif_keymgr_t *keymgr) {
  if (keymgr == NULL) {
    return kDifKeymgrLockableBadArg;
  }

  if (!is_ready(keymgr)) {
    return kDifKeymgrLockableLocked;
  }

  start_operation(keymgr, (start_operation_params_t){
                              .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
                              .op = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_ID,
                          });

  return kDifKeymgrLockableOk;
}

dif_keymgr_lockable_result_t dif_keymgr_generate_versioned_key(
    const dif_keymgr_t *keymgr, dif_keymgr_versioned_key_params_t params) {
  if (keymgr == NULL) {
    return kDifKeymgrLockableBadArg;
  }

  start_operation_params_t hw_op_params;
  switch (params.dest) {
    case kDifKeymgrVersionedKeyDestSw:
      hw_op_params = (start_operation_params_t){
          .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_NONE,
          .op = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_SW_OUTPUT,
      };
      break;
    case kDifKeymgrVersionedKeyDestAes:
      hw_op_params = (start_operation_params_t){
          .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_AES,
          .op = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
      };
      break;
    case kDifKeymgrVersionedKeyDestHmac:
      hw_op_params = (start_operation_params_t){
          .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_HMAC,
          .op = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
      };
      break;
    case kDifKeymgrVersionedKeyDestKmac:
      hw_op_params = (start_operation_params_t){
          .dest = KEYMGR_CONTROL_DEST_SEL_VALUE_KMAC,
          .op = KEYMGR_CONTROL_OPERATION_VALUE_GENERATE_HW_OUTPUT,
      };
      break;
    default:
      return kDifKeymgrLockableBadArg;
  }

  if (!is_ready(keymgr)) {
    return kDifKeymgrLockableLocked;
  }

  // Set salt and version
  mmio_region_memcpy_to_mmio32(keymgr->params.base_addr,
                               KEYMGR_SALT_0_REG_OFFSET, params.salt,
                               sizeof(params.salt));
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_KEY_VERSION_REG_OFFSET,
                      params.version);

  start_operation(keymgr, hw_op_params);

  return kDifKeymgrLockableOk;
}

dif_keymgr_result_t dif_keymgr_sideload_clear_set_enabled(
    const dif_keymgr_t *keymgr, dif_keymgr_toggle_t state) {
  bool enable = false;
  if (keymgr == NULL || !toggle_to_bool(state, &enable)) {
    return kDifKeymgrBadArg;
  }

  mmio_region_write32(
      keymgr->params.base_addr, KEYMGR_SIDELOAD_CLEAR_REG_OFFSET,
      bitfield_bit32_write(0, KEYMGR_SIDELOAD_CLEAR_VAL_BIT, enable));

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_sideload_clear_get_enabled(
    const dif_keymgr_t *keymgr, dif_keymgr_toggle_t *state) {
  if (keymgr == NULL || state == NULL) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(keymgr->params.base_addr,
                                        KEYMGR_SIDELOAD_CLEAR_REG_OFFSET);
  *state = bool_to_toggle(
      bitfield_bit32_read(reg_val, KEYMGR_SIDELOAD_CLEAR_VAL_BIT));

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_read_output(const dif_keymgr_t *keymgr,
                                           dif_keymgr_output_t *output) {
  if (keymgr == NULL || output == NULL) {
    return kDifKeymgrBadArg;
  }

  mmio_region_memcpy_from_mmio32(keymgr->params.base_addr,
                                 KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET,
                                 output->value[0], sizeof(output->value[0]));
  mmio_region_memcpy_from_mmio32(keymgr->params.base_addr,
                                 KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET,
                                 output->value[1], sizeof(output->value[1]));

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_alert_force(const dif_keymgr_t *keymgr,
                                           dif_keymgr_alert_t alert) {
  if (keymgr == NULL) {
    return kDifKeymgrBadArg;
  }

  bitfield_bit32_index_t bit_index;
  switch (alert) {
    case kDifKeymgrAlertHardware:
      bit_index = KEYMGR_ALERT_TEST_FATAL_FAULT_ERR_BIT;
      break;
    case kDifKeymgrAlertSoftware:
      bit_index = KEYMGR_ALERT_TEST_RECOV_OPERATION_ERR_BIT;
      break;
    default:
      return kDifKeymgrBadArg;
  }

  mmio_region_write32(keymgr->params.base_addr, KEYMGR_ALERT_TEST_REG_OFFSET,
                      bitfield_bit32_write(0, bit_index, true));

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_is_pending(const dif_keymgr_t *keymgr,
                                              dif_keymgr_irq_t irq,
                                              bool *is_pending) {
  bitfield_bit32_index_t bit_index;
  if (keymgr == NULL || !get_irq_bit_index(irq, &bit_index) ||
      is_pending == NULL) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(keymgr->params.base_addr,
                                        KEYMGR_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg_val, bit_index);

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_acknowledge(const dif_keymgr_t *keymgr,
                                               dif_keymgr_irq_t irq) {
  bitfield_bit32_index_t bit_index;
  if (keymgr == NULL || !get_irq_bit_index(irq, &bit_index)) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = bitfield_bit32_write(0, bit_index, true);
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_INTR_STATE_REG_OFFSET,
                      reg_val);

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_get_enabled(const dif_keymgr_t *keymgr,
                                               dif_keymgr_irq_t irq,
                                               dif_keymgr_toggle_t *state) {
  bitfield_bit32_index_t bit_index;
  if (keymgr == NULL || !get_irq_bit_index(irq, &bit_index) || state == NULL) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(keymgr->params.base_addr,
                                        KEYMGR_INTR_ENABLE_REG_OFFSET);
  *state = bool_to_toggle(bitfield_bit32_read(reg_val, bit_index));

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_set_enabled(const dif_keymgr_t *keymgr,
                                               dif_keymgr_irq_t irq,
                                               dif_keymgr_toggle_t state) {
  bitfield_bit32_index_t bit_index;
  bool enable = false;
  if (keymgr == NULL || !get_irq_bit_index(irq, &bit_index) ||
      !toggle_to_bool(state, &enable)) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = mmio_region_read32(keymgr->params.base_addr,
                                        KEYMGR_INTR_ENABLE_REG_OFFSET);
  reg_val = bitfield_bit32_write(reg_val, bit_index, enable);
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_INTR_ENABLE_REG_OFFSET,
                      reg_val);

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_force(const dif_keymgr_t *keymgr,
                                         dif_keymgr_irq_t irq) {
  bitfield_bit32_index_t bit_index;
  if (keymgr == NULL || !get_irq_bit_index(irq, &bit_index)) {
    return kDifKeymgrBadArg;
  }

  uint32_t reg_val = bitfield_bit32_write(0, bit_index, true);
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_INTR_TEST_REG_OFFSET,
                      reg_val);

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_disable_all(
    const dif_keymgr_t *keymgr, dif_keymgr_irq_snapshot_t *snapshot) {
  if (keymgr == NULL) {
    return kDifKeymgrBadArg;
  }

  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(keymgr->params.base_addr,
                                   KEYMGR_INTR_ENABLE_REG_OFFSET);
  }
  mmio_region_write32(keymgr->params.base_addr, KEYMGR_INTR_ENABLE_REG_OFFSET,
                      0);

  return kDifKeymgrOk;
}

dif_keymgr_result_t dif_keymgr_irq_restore_all(
    const dif_keymgr_t *keymgr, const dif_keymgr_irq_snapshot_t *snapshot) {
  if (keymgr == NULL || snapshot == NULL) {
    return kDifKeymgrBadArg;
  }

  mmio_region_write32(keymgr->params.base_addr, KEYMGR_INTR_ENABLE_REG_OFFSET,
                      *snapshot);

  return kDifKeymgrOk;
}
