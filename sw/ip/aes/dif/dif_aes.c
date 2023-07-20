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

/**
 * Waits for the given AES status flag to be set the given value.
 *
 * @param aes An aes DIF handle.
 * @param flag Status flag to query.
 * @param value The status flag value.
 */
#define AES_WAIT_FOR_STATUS(aes_, flag_, value_)                      \
  while (mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET, \
                               (flag_)) != value_) {                  \
  }

static bool aes_idle(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_IDLE_BIT);
}

static bool aes_stalled(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_STALL_BIT);
}

static bool aes_output_lost(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_OUTPUT_LOST_BIT);
}

static bool aes_output_valid(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_OUTPUT_VALID_BIT);
}

static bool aes_input_ready(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_INPUT_READY_BIT);
}

static bool aes_alert_fatal(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_ALERT_FATAL_FAULT_BIT);
}

static bool aes_alert_recoverable(const dif_aes_t *aes) {
  return mmio_region_get_bit32(aes->base_addr, AES_STATUS_REG_OFFSET,
                               AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT);
}

static void aes_shadowed_write(mmio_region_t base, ptrdiff_t offset,
                               uint32_t value) {
  mmio_region_write32(base, offset, value);
  mmio_region_write32(base, offset, value);
}

static void aes_clear_internal_state(const dif_aes_t *aes) {
  // Make sure AES is idle before clearing.
  AES_WAIT_FOR_STATUS(aes, AES_STATUS_IDLE_BIT, true);

  // It should be fine to clobber the Control register. Only
  // `AES_CTRL_SHADOWED_MANUAL_OPERATION` bit must be set.
  uint32_t ctrl_reg =
      bitfield_bit32_write(0, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true);

  aes_shadowed_write(aes->base_addr, AES_CTRL_SHADOWED_REG_OFFSET, ctrl_reg);

  uint32_t trigger_reg =
      bitfield_bit32_write(0, AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true);

  trigger_reg =
      bitfield_bit32_write(trigger_reg, AES_TRIGGER_DATA_OUT_CLEAR_BIT, true);

  mmio_region_write32(aes->base_addr, AES_TRIGGER_REG_OFFSET, trigger_reg);

  // Make sure AES is cleared before proceeding (may take multiple cycles).
  AES_WAIT_FOR_STATUS(aes, AES_STATUS_IDLE_BIT, true);
}

/**
 * Configures AES. Is used by every `dif_aes_start_<mode>` function.
 *
 * @param aes AES state data.
 * @param transaction Configuration data, common across all Cipher modes.
 * @return `dif_result_t`.
 */
static dif_result_t configure(const dif_aes_t *aes,
                              const dif_aes_transaction_t *transaction) {
  uint32_t reg = bitfield_field32_write(0, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                        transaction->operation);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD,
                               transaction->mode);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                               transaction->key_len);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD,
                               transaction->mask_reseeding);

  bool flag = transaction->manual_operation == kDifAesManualOperationManual;
  reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, flag);

  flag = transaction->key_provider == kDifAesKeySideload;
  reg = bitfield_bit32_write(reg, AES_CTRL_SHADOWED_SIDELOAD_BIT, flag);

  aes_shadowed_write(aes->base_addr, AES_CTRL_SHADOWED_REG_OFFSET, reg);

  return kDifOk;
}

/**
 * Configures the auxiliary options for AES.
 *
 * @param aes AES state data.
 * @param transaction Configuration data, common across all Cipher modes.
 * @return `dif_result_t`.
 */
static dif_result_t configure_aux(const dif_aes_t *aes,
                                  const dif_aes_transaction_t *transaction) {
  // Return an error in case the register is locked with different values.
  uint32_t reg_val =
      mmio_region_read32(aes->base_addr, AES_CTRL_AUX_REGWEN_REG_OFFSET);
  if (!reg_val) {
    reg_val =
        mmio_region_read32(aes->base_addr, AES_CTRL_AUX_SHADOWED_REG_OFFSET);
    if (bitfield_bit32_read(
            reg_val, AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT) !=
            transaction->reseed_on_key_change ||
        bitfield_bit32_read(reg_val, AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT) !=
            transaction->force_masks) {
      return kDifError;
    }
    return kDifOk;
  }

  reg_val =
      bitfield_bit32_write(0, AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT,
                           transaction->reseed_on_key_change);
  reg_val = bitfield_bit32_write(reg_val, AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT,
                                 transaction->force_masks);
  aes_shadowed_write(aes->base_addr, AES_CTRL_AUX_SHADOWED_REG_OFFSET, reg_val);

  reg_val = transaction->ctrl_aux_lock == false;
  mmio_region_write32(aes->base_addr, AES_CTRL_AUX_REGWEN_REG_OFFSET, reg_val);

  return kDifOk;
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
    ptrdiff_t offset = reg0_offset + (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t);

    mmio_region_write32(aes->base_addr, offset, data[i]);
  }
}

static void aes_read_multireg(const dif_aes_t *aes, uint32_t *data,
                              size_t regs_num, ptrdiff_t reg0_offset) {
  for (int i = 0; i < regs_num; ++i) {
    ptrdiff_t offset = reg0_offset + (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t);

    data[i] = mmio_region_read32(aes->base_addr, offset);
  }
}

dif_result_t dif_aes_reset(const dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifBadArg;
  }

  aes_clear_internal_state(aes);

  // Any values would do, illegal values chosen here.
  uint32_t reg = bitfield_field32_write(0, AES_CTRL_SHADOWED_OPERATION_FIELD,
                                        AES_CTRL_SHADOWED_OPERATION_MASK);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_MODE_FIELD,
                               AES_CTRL_SHADOWED_MODE_VALUE_AES_NONE);

  reg = bitfield_field32_write(reg, AES_CTRL_SHADOWED_KEY_LEN_FIELD,
                               AES_CTRL_SHADOWED_KEY_LEN_MASK);

  aes_shadowed_write(aes->base_addr, AES_CTRL_SHADOWED_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_aes_start(const dif_aes_t *aes,
                           const dif_aes_transaction_t *transaction,
                           const dif_aes_key_share_t *key,
                           const dif_aes_iv_t *iv) {
  if (aes == NULL || transaction == NULL ||
      (iv == NULL && transaction->mode != kDifAesModeEcb) ||
      (key == NULL &&
       transaction->key_provider == kDifAesKeySoftwareProvided)) {
    return kDifBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifUnavailable;
  }

  dif_result_t result = configure(aes, transaction);
  if (result != kDifOk) {
    return result;
  }

  result = configure_aux(aes, transaction);
  if (result != kDifOk) {
    return result;
  }

  if (transaction->key_provider == kDifAesKeySoftwareProvided) {
    aes_set_multireg(aes, &key->share0[0], AES_KEY_SHARE0_MULTIREG_COUNT,
                     AES_KEY_SHARE0_0_REG_OFFSET);

    aes_set_multireg(aes, &key->share1[0], AES_KEY_SHARE1_MULTIREG_COUNT,
                     AES_KEY_SHARE1_0_REG_OFFSET);
  }

  if (transaction->mode != kDifAesModeEcb) {
    // Make sure AES is idle before providing the IV. Depending on the
    // configuration, updating the key might cause the AES to become non-idle
    // and reseed the internal PRNGs.
    AES_WAIT_FOR_STATUS(aes, AES_STATUS_IDLE_BIT, true);
    aes_set_multireg(aes, &iv->iv[0], AES_IV_MULTIREG_COUNT,
                     AES_IV_0_REG_OFFSET);
  }

  return kDifOk;
}

dif_result_t dif_aes_end(const dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifUnavailable;
  }

  aes_clear_internal_state(aes);

  return kDifOk;
}

dif_result_t dif_aes_load_data(const dif_aes_t *aes,
                               const dif_aes_data_t data) {
  if (aes == NULL) {
    return kDifBadArg;
  }

  if (!aes_input_ready(aes)) {
    return kDifUnavailable;
  }

  aes_set_multireg(aes, &data.data[0], AES_DATA_IN_MULTIREG_COUNT,
                   AES_DATA_IN_0_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_aes_read_output(const dif_aes_t *aes, dif_aes_data_t *data) {
  if (aes == NULL || data == NULL) {
    return kDifBadArg;
  }

  if (!aes_output_valid(aes)) {
    return kDifError;
  }

  aes_read_multireg(aes, data->data, AES_DATA_OUT_MULTIREG_COUNT,
                    AES_DATA_OUT_0_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_aes_process_data(const dif_aes_t *aes,
                                  const dif_aes_data_t *plain_text,
                                  dif_aes_data_t *cipher_text,
                                  size_t block_count) {
  if (aes == NULL || plain_text == NULL || cipher_text == NULL ||
      block_count == 0) {
    return kDifBadArg;
  }

  // The algorithm below just makes sense for at least 2 blocks. Otherwise
  // it is better to use the `load_data` and `read_output` functions.
  if (block_count < 2) {
    DIF_RETURN_IF_ERROR(dif_aes_load_data(aes, plain_text[0]));
    return dif_aes_read_output(aes, cipher_text);
  }

  // Ensure that the INPUT_READY bit in STATUS is 1.
  if (!aes_input_ready(aes)) {
    return kDifUnavailable;
  }

  // Write Input Data Block 0 to the Input Data registers DATA_IN_0 - DATA_IN_3.
  aes_set_multireg(aes, plain_text[0].data, AES_DATA_IN_MULTIREG_COUNT,
                   AES_DATA_IN_0_REG_OFFSET);

  // Wait for the INPUT_READY bit in STATUS to become 1, i.e. wait for the AES
  // unit to load Input Data Block 0 into the internal state register and start
  // operation.
  AES_WAIT_FOR_STATUS(aes, AES_STATUS_INPUT_READY_BIT, true);
  // Then for every Data Block I=0,..,N-3, software must:
  for (size_t i = 0; i < block_count; ++i) {
    // Write Input Data Block I+1 into the Input Data register. There is no need
    // to explicitly check INPUT_READY as in the same cycle OUTPUT_VALID becomes
    // 1, the current input is loaded in (meaning INPUT_READY becomes 1 one
    // cycle later).
    if (i + 1 < block_count) {
      aes_set_multireg(aes, plain_text[i + 1].data, AES_DATA_IN_MULTIREG_COUNT,
                       AES_DATA_IN_0_REG_OFFSET);
    }

    // Wait for the OUTPUT_VALID bit in STATUS to become 1, i.e., wait for the
    // AES unit to finish encryption/decryption of Block I. The AES unit then
    // directly starts processing the previously input block I+1.
    AES_WAIT_FOR_STATUS(aes, AES_STATUS_OUTPUT_VALID_BIT, true);

    // Read Output Data Block I from the Output Data registers DATA_OUT_0 -
    // DATA_OUT_3. Each register must be read at least once.
    aes_read_multireg(aes, cipher_text[i].data, AES_DATA_OUT_MULTIREG_COUNT,
                      AES_DATA_OUT_0_REG_OFFSET);
  }

  return kDifOk;
}

dif_result_t dif_aes_trigger(const dif_aes_t *aes, dif_aes_trigger_t trigger) {
  if (aes == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, trigger, true);
  mmio_region_write32(aes->base_addr, AES_TRIGGER_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_aes_get_status(const dif_aes_t *aes, dif_aes_status_t flag,
                                bool *set) {
  if (aes == NULL || set == NULL) {
    return kDifBadArg;
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
      return kDifError;
  }

  return kDifOk;
}

dif_result_t dif_aes_read_iv(const dif_aes_t *aes, dif_aes_iv_t *iv) {
  if (aes == NULL || iv == NULL) {
    return kDifBadArg;
  }

  if (!aes_idle(aes)) {
    return kDifUnavailable;
  }

  for (int i = 0; i < AES_IV_MULTIREG_COUNT; ++i) {
    ptrdiff_t offset =
        AES_IV_0_REG_OFFSET + (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t);

    iv->iv[i] = mmio_region_read32(aes->base_addr, offset);
  }
  return kDifOk;
}
