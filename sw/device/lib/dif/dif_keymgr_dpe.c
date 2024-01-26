// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_keymgr_dpe.h"

#include <assert.h>

#include "sw/device/lib/dif/dif_base.h"

#include "keymgr_dpe_regs.h"  // Generated.
#include "sw/device/lib/dif/autogen/dif_keymgr_dpe_autogen.h"

/**
 * Address spaces of SW_BINDING_N, SALT_N, SW_SHARE0_OUTPUT_N, and
 * SW_SHARE1_OUTPUT_N registers must be contiguous to be able to use
 * `mmio_region_memcpy_to/from_mmio32()`.
 */
static_assert(KEYMGR_DPE_SW_BINDING_1_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 4,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_2_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 8,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_3_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 12,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_4_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 16,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_5_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 20,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_6_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 24,
              "SW_BINDING_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_BINDING_7_REG_OFFSET ==
                  KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + 28,
              "SW_BINDING_N registers must be contiguous.");

static_assert(KEYMGR_DPE_SALT_1_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 4,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_2_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 8,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_3_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 12,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_4_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 16,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_5_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 20,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_6_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 24,
              "SALT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SALT_7_REG_OFFSET == KEYMGR_DPE_SALT_0_REG_OFFSET + 28,
              "SALT_N registers must be contiguous.");

static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_1_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 4,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_2_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 8,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_3_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 12,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_4_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 16,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_5_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 20,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_6_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 24,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE0_OUTPUT_7_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET + 28,
              "SW_SHARE0_OUTPUT_N registers must be contiguous.");

static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_1_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 4,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_2_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 8,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_3_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 12,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_4_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 16,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_5_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 20,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_6_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 24,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");
static_assert(KEYMGR_DPE_SW_SHARE1_OUTPUT_7_REG_OFFSET ==
                  KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET + 28,
              "SW_SHARE1_OUTPUT_N registers must be contiguous.");

/**
 * Error code constants of `dif_keymgr_dpe_status_code_t` are masks for the bits
 * of ERR_CODE register shifted left by 1.
 */
static_assert(kDifKeymgrDpeStatusCodeInvalidOperation >> 1 ==
                  1 << KEYMGR_DPE_ERR_CODE_INVALID_OP_BIT,
              "Layout of ERR_CODE register changed.");
static_assert(kDifKeymgrDpeStatusCodeInvalidKmacInput >> 1 ==
                  1 << KEYMGR_DPE_ERR_CODE_INVALID_KMAC_INPUT_BIT,
              "Layout of ERR_CODE register changed.");

/**
 * Ensure that enum values for versioned key generation match the parameters
 * generated by HW.
 */
static_assert(kDifKeymgrDpeKeyDestAes ==
                  KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_AES,
              "Key destination macros must match the values from its enum.");
static_assert(kDifKeymgrDpeKeyDestKmac ==
                  KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_KMAC,
              "Key destination macros must match the values from its enum.");
static_assert(kDifKeymgrDpeKeyDestOtbn ==
                  KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN,
              "Key destination macros must match the values from its enum.");

/**
 * Ensure that SW-visible FSM values match the one defined as SW enum.
 */
static_assert(kDifKeymgrDpeStateReset ==
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_RESET,
              "Keymgr_DPE reported FSM state and SW enums must match.");
static_assert(kDifKeymgrDpeStateAvailable ==
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
              "Keymgr_DPE reported FSM state and SW enums must match.");
static_assert(kDifKeymgrDpeStateDisabled ==
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_DISABLED,
              "Keymgr_DPE reported FSM state and SW enums must match.");
static_assert(kDifKeymgrDpeStateInvalid ==
                  KEYMGR_DPE_WORKING_STATE_STATE_VALUE_INVALID,
              "Keymgr_DPE reported FSM state and SW enums must match.");

/**
 * Checks if the key manager is ready for a new operation, i.e. it is idle and
 * the CONFIG register is unlocked.
 */
OT_WARN_UNUSED_RESULT
static bool is_ready(const dif_keymgr_dpe_t *keymgr_dpe) {
  // KeymgrDPE must be idle and the CONTROL register must be writable.
  uint32_t reg_op_status = mmio_region_read32(keymgr_dpe->base_addr,
                                              KEYMGR_DPE_OP_STATUS_REG_OFFSET);
  if (bitfield_field32_read(reg_op_status, KEYMGR_DPE_OP_STATUS_STATUS_FIELD) !=
      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE) {
    return false;
  }
  uint32_t reg_cfg_regwen = mmio_region_read32(
      keymgr_dpe->base_addr, KEYMGR_DPE_CFG_REGWEN_REG_OFFSET);
  return bitfield_bit32_read(reg_cfg_regwen, KEYMGR_DPE_CFG_REGWEN_EN_BIT);
}

dif_result_t dif_keymgr_dpe_initialize(const dif_keymgr_dpe_t *keymgr_dpe,
                                       uint32_t slot_dst_sel) {
  if (keymgr_dpe == NULL) {
    return kDifBadArg;
  }

  if (!is_ready(keymgr_dpe)) {
    return kDifLocked;
  }

  uint32_t reg_control = bitfield_field32_write(
      KEYMGR_DPE_CONTROL_SHADOWED_REG_RESVAL,
      KEYMGR_DPE_CONTROL_SHADOWED_SLOT_DST_SEL_FIELD, slot_dst_sel);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE);
  mmio_region_write32_shadowed(keymgr_dpe->base_addr,
                               KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET,
                               reg_control);

  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_START_REG_OFFSET,
                      1 << KEYMGR_DPE_START_EN_BIT);

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_advance_state(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_advance_params_t *params) {
  if (keymgr_dpe == NULL || params == NULL) {
    return kDifBadArg;
  }

  if (!is_ready(keymgr_dpe)) {
    return kDifLocked;
  }

  // If either of SLOT_POLICY_REGWEN, MAX_KEY_VER_REGWEN or SW_BINDING_REGWEN is
  // locked, return error.
  uint32_t slot_policy_regwen = mmio_region_read32(
      keymgr_dpe->base_addr, KEYMGR_DPE_SLOT_POLICY_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(slot_policy_regwen,
                           KEYMGR_DPE_SLOT_POLICY_REGWEN_EN_BIT)) {
    return kDifLocked;
  }

  uint32_t reg_max_key_ver_wen = mmio_region_read32(
      keymgr_dpe->base_addr, KEYMGR_DPE_MAX_KEY_VER_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(reg_max_key_ver_wen,
                           KEYMGR_DPE_MAX_KEY_VER_REGWEN_EN_BIT)) {
    return kDifLocked;
  }

  uint32_t sw_binding_regwen = mmio_region_read32(
      keymgr_dpe->base_addr, KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(sw_binding_regwen,
                           KEYMGR_DPE_SW_BINDING_REGWEN_EN_BIT)) {
    return kDifLocked;
  }

  // Now that we know REGWEN registers are enabled, we can write each value and
  // then lock REGWEN registers (rw0c).
  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_SLOT_POLICY_REG_OFFSET,
                      params->slot_policy);
  mmio_region_write32(keymgr_dpe->base_addr,
                      KEYMGR_DPE_SLOT_POLICY_REGWEN_REG_OFFSET, 0);

  mmio_region_write32_shadowed(keymgr_dpe->base_addr,
                               KEYMGR_DPE_MAX_KEY_VER_SHADOWED_REG_OFFSET,
                               params->max_key_version);
  mmio_region_write32(keymgr_dpe->base_addr,
                      KEYMGR_DPE_MAX_KEY_VER_REGWEN_REG_OFFSET, 0);

  mmio_region_memcpy_to_mmio32(
      keymgr_dpe->base_addr, KEYMGR_DPE_SW_BINDING_0_REG_OFFSET,
      params->binding_value, sizeof(params->binding_value));
  mmio_region_write32(keymgr_dpe->base_addr,
                      KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 0);

  uint32_t reg_control = bitfield_field32_write(
      KEYMGR_DPE_CONTROL_SHADOWED_REG_RESVAL,
      KEYMGR_DPE_CONTROL_SHADOWED_SLOT_SRC_SEL_FIELD, params->slot_src_sel);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_DPE_CONTROL_SHADOWED_SLOT_DST_SEL_FIELD,
      params->slot_dst_sel);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE);
  mmio_region_write32_shadowed(keymgr_dpe->base_addr,
                               KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET,
                               reg_control);
  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_START_REG_OFFSET,
                      1 << KEYMGR_DPE_START_EN_BIT);

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_erase_slot(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_erase_params_t *params) {
  if (keymgr_dpe == NULL) {
    return kDifBadArg;
  }

  if (!is_ready(keymgr_dpe)) {
    return kDifLocked;
  }

  uint32_t reg_control = bitfield_field32_write(
      KEYMGR_DPE_CONTROL_SHADOWED_REG_RESVAL,
      KEYMGR_DPE_CONTROL_SHADOWED_SLOT_DST_SEL_FIELD, params->slot_dst_sel);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ERASE_SLOT);
  mmio_region_write32_shadowed(keymgr_dpe->base_addr,
                               KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET,
                               reg_control);
  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_START_REG_OFFSET,
                      1 << KEYMGR_DPE_START_EN_BIT);

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_generate(
    const dif_keymgr_dpe_t *keymgr_dpe,
    const dif_keymgr_dpe_generate_params_t *params) {
  if (keymgr_dpe == NULL || params == NULL) {
    return kDifBadArg;
  }

  if (!is_ready(keymgr_dpe)) {
    return kDifLocked;
  }

  uint32_t reg_control = bitfield_field32_write(
      KEYMGR_DPE_CONTROL_SHADOWED_REG_RESVAL,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_FIELD, params->key_dest);
  reg_control = bitfield_field32_write(
      reg_control, KEYMGR_DPE_CONTROL_SHADOWED_SLOT_SRC_SEL_FIELD,
      params->slot_src_sel);

  if (params->sideload_key) {
    reg_control = bitfield_field32_write(
        reg_control, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD,
        KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT);
  } else {
    reg_control = bitfield_field32_write(
        reg_control, KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_FIELD,
        KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_SW_OUTPUT);
  }
  mmio_region_write32_shadowed(keymgr_dpe->base_addr,
                               KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET,
                               reg_control);

  // Write SALT and VERSION.
  mmio_region_memcpy_to_mmio32(keymgr_dpe->base_addr,
                               KEYMGR_DPE_SALT_0_REG_OFFSET, params->salt,
                               sizeof(params->salt));
  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_KEY_VERSION_REG_OFFSET,
                      params->version);

  // Start the operation
  mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_START_REG_OFFSET,
                      1 << KEYMGR_DPE_START_EN_BIT);

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_read_output(const dif_keymgr_dpe_t *keymgr_dpe,
                                        dif_keymgr_dpe_output_t *output) {
  if (keymgr_dpe == NULL || output == NULL) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(keymgr_dpe->base_addr,
                                 KEYMGR_DPE_SW_SHARE0_OUTPUT_0_REG_OFFSET,
                                 output->value[0], sizeof(output->value[0]));
  mmio_region_memcpy_from_mmio32(keymgr_dpe->base_addr,
                                 KEYMGR_DPE_SW_SHARE1_OUTPUT_0_REG_OFFSET,
                                 output->value[1], sizeof(output->value[1]));

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_get_status_codes(
    const dif_keymgr_dpe_t *keymgr_dpe,
    dif_keymgr_dpe_status_codes_t *status_codes) {
  if (keymgr_dpe == NULL || status_codes == NULL) {
    return kDifBadArg;
  }

  // Read and clear OP_STATUS register (rw1c).
  uint32_t reg_op_status = mmio_region_read32(keymgr_dpe->base_addr,
                                              KEYMGR_DPE_OP_STATUS_REG_OFFSET);

  bool is_idle = false;
  bool has_error = false;
  switch (reg_op_status) {
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE:
      is_idle = true;
      break;
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS:
      is_idle = true;
      mmio_region_write32(keymgr_dpe->base_addr,
                          KEYMGR_DPE_OP_STATUS_REG_OFFSET, reg_op_status);
      break;
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR:
      is_idle = true;
      has_error = true;
      mmio_region_write32(keymgr_dpe->base_addr,
                          KEYMGR_DPE_OP_STATUS_REG_OFFSET, reg_op_status);
      break;
    case KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP:
      break;
    default:
      return kDifError;
  }

  // `kIdleBitfield` defines the idle field within
  // `dif_keymgr_dpe_status_codes_t`.
  *status_codes = (dif_keymgr_dpe_status_codes_t)bitfield_field32_write(
      0, kIdleBitfield, is_idle);

  if (has_error) {
    // Read and clear ERR_CODE register (rw1c).
    uint32_t reg_err_code = mmio_region_read32(keymgr_dpe->base_addr,
                                               KEYMGR_DPE_ERR_CODE_REG_OFFSET);
    mmio_region_write32(keymgr_dpe->base_addr, KEYMGR_DPE_ERR_CODE_REG_OFFSET,
                        reg_err_code);
    *status_codes = (dif_keymgr_dpe_status_codes_t)bitfield_field32_write(
        *status_codes, kErrorBitfield, reg_err_code);
  }

  return kDifOk;
}

dif_result_t dif_keymgr_dpe_get_state(const dif_keymgr_dpe_t *keymgr_dpe,
                                      dif_keymgr_dpe_state_t *state) {
  if (keymgr_dpe == NULL || state == NULL) {
    return kDifBadArg;
  }

  uint32_t reg_state = mmio_region_read32(keymgr_dpe->base_addr,
                                          KEYMGR_DPE_WORKING_STATE_REG_OFFSET);

  *state =
      bitfield_field32_read(reg_state, KEYMGR_DPE_WORKING_STATE_STATE_FIELD);
  return kDifOk;
}
