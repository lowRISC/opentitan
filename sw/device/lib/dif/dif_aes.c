// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aes.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "aes_regs.h"  // Generated.

/*
 * From: https://docs.opentitan.org/hw/ip/aes/doc/index.html#register-table,
 * aes.CTRL.
 */

/*
 * Field to select AES block cipher mode.
 *
 * Invalid input values, i.e., value with multiple bits set - are mapped to
 * `kAesModeFieldValNone`.
 */
typedef enum aes_mode_field_val {
  kAesModeFieldValEcb = 0x01,  /**< The Electronic Codebook Mode. */
  kAesModeFieldValCbc = 0x02,  /**< The Cipher Block Chaining Mode. */
  kAesModeFieldValCfb = 0x04,  /**< TODO */
  kAesModeFieldValOfb = 0x08,  /**< TODO */
  kAesModeFieldValCtr = 0x10,  /**< The Counter Mode. */
  kAesModeFieldValNone = 0x20, /**< TODO */
} aes_mode_field_val_t;

/*
 * Field to select AES key length.
 *
 * Invalid input values, i.e., value with multiple bits set, value 3'b000, and
 * value 3'b010 in case 192-bit keys are not supported (disabled at compile
 * time) are mapped to `kAesKeyFieldVal256`.
 */
typedef enum aes_key_field_val {
  kAesKeyFieldValInvalid = 0x00,
  kAesKeyFieldVal128 = 0x01,
  kAesKeyFieldVal192 = 0x02,
  kAesKeyFieldVal256 = 0x04,
} aes_key_field_val_t;

static bool aes_idle(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_IDLE_BIT);
}

static bool aes_stalled(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_STALL_BIT);
}

static bool aes_output_lost(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_OUTPUT_LOST_BIT);
}

static bool aes_output_valid(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_OUTPUT_VALID_BIT);
}

static bool aes_input_ready(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_INPUT_READY_BIT);
}

static bool aes_alert_fatal(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_ALERT_FATAL_FAULT_BIT);
}

static bool aes_alert_recoverable(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->params.base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT);
}

static void aes_shadowed_write(mmio_region_t base, ptrdiff_t offset,
                               uint32_t value) {
  mmio_region_write32(base, offset, value);
  mmio_region_write32(base, offset, value);
}

static void aes_clear_internal_state(const dif_aes_t *aes) {
  // Make sure AES is idle before clearing.
  while (!aes_idle(aes)) {
  }

  // It should be fine to clobber the Control register. Only
  // `AES_CTRL_SHADOWED_MANUAL_OPERATION` bit must be set.
  uint32_t ctrl_reg =
      bitfield_bit32_write(0, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);

  aes_shadowed_write(aes->params.base_addr, AES_CTRL_SHADOWED_REG_OFFSET,
                     ctrl_reg);

  uint32_t trigger_reg =
      bitfield_bit32_write(0, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);

  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);

  mmio_region_write32(aes->params.base_addr, AES_TRIGGER_REG_OFFSET,
                      trigger_reg);

  // Make sure AES is cleared before proceeding (may take multiple cycles).
  while (!aes_idle(aes)) {
  }
}

static aes_key_field_val_t key_to_field(dif_aes_key_length_t key) {
  switch (key) {
    case kDifAesKey128:
      return kAesKeyFieldVal128;
    case kDifAesKey192:
      return kAesKeyFieldVal192;
    case kDifAesKey256:
      return kAesKeyFieldVal256;
    default:
      return kAesKeyFieldValInvalid;
  }
}

/**
 * Configures AES. Is used by every `dif_aes_start_<mode>` function.
 *
 * @param aes AES state data.
 * @param transaction Configuration data, common across all Cipher modes.
 * @param cipher_mode_val Cipher Mode register write value.
 * @return `dif_aes_start_result_t`.
 */
static dif_aes_start_result_t configure(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    aes_mode_field_val_t cipher_mode_val) {
  aes_key_field_val_t key_len_val = key_to_field(transaction->key_len);
  if (key_len_val == kAesKeyFieldValInvalid) {
    return kDifAesStartError;
  }

  uint32_t reg =
      bitfield_field32_write(0, AES_CTRL_SHADOWED_KEY_LEN_FIELD, key_len_val);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD,
                               cipher_mode_val);

  if (transaction->mode == kDifAesModeDecrypt) {
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_OPERATION_BIT, true);
  } else {
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_OPERATION_BIT, false);
  }

  if (transaction->operation == kDifAesOperationManual) {
    reg =
        bitfield_bit32_write(reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);
  } else {
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT,
                               false);
  }

  if (transaction->masking == kDifAesMaskingForceZero) {
    reg =
        bitfield_bit32_write(reg, AES_CTRL_SHADOWED_FORCE_ZERO_MASKS_BIT, true);
  } else {
    reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_FORCE_ZERO_MASKS_BIT,
                               false);
  }

  aes_shadowed_write(aes->params.base_addr, AES_CTRL_SHADOWED_REG_OFFSET, reg);

  return kDifAesStartOk;
}

/**
 * Sets all "sub-registers" of `aes.KEY`, `aes.IV` or `aes.DATA_IN` multiregs.
 *
 * @param aes AES state data.
 * @param data Data to be written into multi-reg registers.
 * @param regs_num Number of "sub-registers" in the multireg.
 * @param reg0_offset Offset to the "sub-register 0" in the multireg.
 */
static void aes_set_multireg(const dif_aes_t *aes, const uint32_t *data,
                             size_t regs_num, ptrdiff_t reg0_offset) {
  for (int i = 0; i < regs_num; ++i) {
    ptrdiff_t offset = reg0_offset + (i * sizeof(uint32_t));

    mmio_region_write32(aes->params.base_addr, offset, data[i]);
  }
}

dif_aes_result_t dif_aes_init(dif_aes_params_t params, dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifAesBadArg;
  }

  aes->params = params;

  return kDifAesOk;
}

dif_aes_reset_result_t dif_aes_reset(const dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifAesResetBadArg;
  }

  aes_clear_internal_state(aes);

  uint32_t reg =
      bitfield_bit32_write(0, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);

  // Any values would do, illegal values chosen here.
  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD,
                               AES_CTRL_SHADOWED_MODE_VALUE_AES_NONE);

  reg =
      bitfield_field32_write(reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD, 0xffffffff);

  aes_shadowed_write(aes->params.base_addr, AES_CTRL_SHADOWED_REG_OFFSET, reg);

  return kDifAesResetOk;
}

dif_aes_start_result_t dif_aes_start_ecb(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key) {
  if (aes == NULL || transaction == NULL) {
    return kDifAesStartBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifAesStartBusy;
  }

  dif_aes_start_result_t result =
      configure(aes, transaction, kAesModeFieldValEcb);
  if (result != kDifAesStartOk) {
    return result;
  }

  aes_set_multireg(aes, &key.share0[0], AES_KEY_SHARE0_MULTIREG_COUNT,
                   AES_KEY_SHARE0_0_REG_OFFSET);

  aes_set_multireg(aes, &key.share1[0], AES_KEY_SHARE1_MULTIREG_COUNT,
                   AES_KEY_SHARE1_0_REG_OFFSET);

  return kDifAesStartOk;
}

dif_aes_start_result_t dif_aes_start_cbc(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key, dif_aes_iv_t iv) {
  if (aes == NULL || transaction == NULL) {
    return kDifAesStartBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifAesStartBusy;
  }

  dif_aes_start_result_t result =
      configure(aes, transaction, kAesModeFieldValCbc);
  if (result != kDifAesStartOk) {
    return result;
  }

  aes_set_multireg(aes, &key.share0[0], AES_KEY_SHARE0_MULTIREG_COUNT,
                   AES_KEY_SHARE0_0_REG_OFFSET);

  aes_set_multireg(aes, &key.share1[0], AES_KEY_SHARE1_MULTIREG_COUNT,
                   AES_KEY_SHARE1_0_REG_OFFSET);

  aes_set_multireg(aes, &iv.iv[0], AES_IV_MULTIREG_COUNT, AES_IV_0_REG_OFFSET);

  return kDifAesStartOk;
}

dif_aes_start_result_t dif_aes_start_ctr(
    const dif_aes_t *aes, const dif_aes_transaction_t *transaction,
    dif_aes_key_share_t key, dif_aes_iv_t iv) {
  if (aes == NULL || transaction == NULL) {
    return kDifAesStartBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifAesStartBusy;
  }

  dif_aes_start_result_t result =
      configure(aes, transaction, kAesModeFieldValCtr);
  if (result != kDifAesStartOk) {
    return result;
  }

  aes_set_multireg(aes, &key.share0[0], AES_KEY_SHARE0_MULTIREG_COUNT,
                   AES_KEY_SHARE0_0_REG_OFFSET);

  aes_set_multireg(aes, &key.share1[0], AES_KEY_SHARE1_MULTIREG_COUNT,
                   AES_KEY_SHARE1_0_REG_OFFSET);

  aes_set_multireg(aes, &iv.iv[0], AES_IV_MULTIREG_COUNT, AES_IV_0_REG_OFFSET);

  return kDifAesStartOk;
}

dif_aes_end_result_t dif_aes_end(const dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifAesEndBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifAesEndBusy;
  }

  aes_clear_internal_state(aes);

  return kDifAesEndOk;
}

dif_aes_load_data_result_t dif_aes_load_data(const dif_aes_t *aes,
                                             const dif_aes_data_t data) {
  if (aes == NULL) {
    return kDifAesLoadDataBadArg;
  }

  if (!aes_input_ready(aes)) {
    return kDifAesLoadDataBusy;
  }

  aes_set_multireg(aes, &data.data[0], AES_DATA_IN_MULTIREG_COUNT,
                   AES_DATA_IN_0_REG_OFFSET);

  return kDifAesLoadDataOk;
}

dif_aes_read_output_result_t dif_aes_read_output(const dif_aes_t *aes,
                                                 dif_aes_data_t *data) {
  if (aes == NULL || data == NULL) {
    return kDifAesReadOutputBadArg;
  }

  if (!aes_output_valid(aes)) {
    return kDifAesReadOutputInvalid;
  }

  for (int i = 0; i < AES_DATA_OUT_MULTIREG_COUNT; ++i) {
    ptrdiff_t offset = AES_DATA_OUT_0_REG_OFFSET + (i * sizeof(uint32_t));

    data->data[i] = mmio_region_read32(aes->params.base_addr, offset);
  }

  return kDifAesReadOutputOk;
}

dif_aes_result_t dif_aes_trigger(const dif_aes_t *aes,
                                 dif_aes_trigger_t trigger) {
  if (aes == NULL) {
    return kDifAesBadArg;
  }

  uint32_t reg;
  switch (trigger) {
    case kDifAesTriggerStart:
      reg = bitfield_bit32_write(0, AES_TRIGGER_START_BIT, true);
      break;
    case kDifAesTriggerKeyIvDataInClear:
      reg = bitfield_bit32_write(0, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);
      break;
    case kDifAesTriggerDataOutClear:
      reg = bitfield_bit32_write(0, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);
      break;
    case kDifAesTriggerPrngReseed:
      reg = bitfield_bit32_write(0, AES_TRIGGER_PRNG_RESEED_BIT, true);
      break;
    default:
      return kDifAesError;
  }

  mmio_region_write32(aes->params.base_addr, AES_TRIGGER_REG_OFFSET, reg);

  return kDifAesOk;
}

dif_aes_result_t dif_aes_get_status(const dif_aes_t *aes, dif_aes_status_t flag,
                                    bool *set) {
  if (aes == NULL || set == NULL) {
    return kDifAesBadArg;
  }

  switch (flag) {
    case kDifAesStatusIdle:
      *set = aes_idle(aes);
      break;
    case kDifAesStatusStall:
      *set = aes_stalled(aes);
      break;
    case kDifAesStatusOutputLost:
      *set = aes_output_lost(aes);
      break;
    case kDifAesStatusOutputValid:
      *set = aes_output_valid(aes);
      break;
    case kDifAesStatusInputReady:
      *set = aes_input_ready(aes);
      break;
    case kDifAesStatusAlertFatalFault:
      *set = aes_alert_fatal(aes);
      break;
    case kDifAesStatusAlertRecovCtrlUpdateErr:
      *set = aes_alert_recoverable(aes);
      break;
    default:
      return kDifAesError;
  }

  return kDifAesOk;
}

DIF_WARN_UNUSED_RESULT
dif_aes_result_t dif_aes_alert_force(const dif_aes_t *aes,
                                     dif_aes_alert_t alert) {
  if (aes == NULL) {
    return kDifAesBadArg;
  }

  bitfield_bit32_index_t index;
  switch (alert) {
    case kDifAlertFatalFault:
      index = AES_ALERT_TEST_FATAL_FAULT_BIT;
      break;
    case kDifAlertRecovCtrlUpdateErr:
      index = AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT;
      break;
    default:
      return kDifAesError;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(aes->params.base_addr, AES_ALERT_TEST_REG_OFFSET, reg);

  return kDifAesOk;
}
