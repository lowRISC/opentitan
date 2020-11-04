// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otp_ctrl.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "otp_ctrl_regs.h"  // Generated.

dif_otp_ctrl_result_t dif_otp_ctrl_init(dif_otp_ctrl_params_t params,
                                        dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  otp->params = params;
  return kDifOtpCtrlOk;
}

/**
 * Checks if integrity/consistency-check-related operations are locked.
 *
 * This is a convenience function to avoid superfluous error-checking in all the
 * functions that can be locked out by this register.
 */
static bool checks_are_locked(const dif_otp_ctrl_t *otp) {
  uint32_t locked = mmio_region_read32(otp->params.base_addr,
                                       OTP_CTRL_CHECK_REGWEN_REG_OFFSET);
  return !bitfield_bit32_read(locked, OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT);
}

dif_otp_ctrl_lockable_result_t dif_otp_ctrl_configure(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_config_t config) {
  if (otp == NULL) {
    return kDifOtpCtrlLockableBadArg;
  }
  if (checks_are_locked(otp)) {
    return kDifOtpCtrlLockableLocked;
  }

  mmio_region_write32(otp->params.base_addr, OTP_CTRL_CHECK_TIMEOUT_REG_OFFSET,
                      config.check_timeout);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_INTEGRITY_CHECK_PERIOD_REG_OFFSET,
                      config.integrity_period_mask);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_CONSISTENCY_CHECK_PERIOD_REG_OFFSET,
                      config.consistency_period_mask);

  return kDifOtpCtrlLockableOk;
}

dif_otp_ctrl_lockable_result_t dif_otp_ctrl_check_integrity(
    const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifOtpCtrlLockableBadArg;
  }
  if (checks_are_locked(otp)) {
    return kDifOtpCtrlLockableLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_TRIGGER_INTEGRITY_BIT, true);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_CHECK_TRIGGER_REG_OFFSET,
                      reg);

  return kDifOtpCtrlLockableOk;
}

dif_otp_ctrl_lockable_result_t dif_otp_ctrl_check_consistency(
    const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifOtpCtrlLockableBadArg;
  }
  if (checks_are_locked(otp)) {
    return kDifOtpCtrlLockableLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_BIT, true);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_CHECK_TRIGGER_REG_OFFSET,
                      reg);

  return kDifOtpCtrlLockableOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_lock_config(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, true);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_CHECK_REGWEN_REG_OFFSET,
                      reg);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_config_is_locked(const dif_otp_ctrl_t *otp,
                                                    bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifOtpCtrlBadArg;
  }

  *is_locked = checks_are_locked(otp);
  return kDifOtpCtrlOk;
}

static bool sw_read_lock_reg_offset(dif_otp_ctrl_partition_t partition,
                                    ptrdiff_t *reg_offset,
                                    bitfield_bit32_index_t *index) {
  switch (partition) {
    case kDifOtpCtrlPartitionCreatorSwCfg:
      *reg_offset = OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_REG_OFFSET;
      *index = OTP_CTRL_CREATOR_SW_CFG_READ_LOCK_CREATOR_SW_CFG_READ_LOCK_BIT;
      break;
    case kDifOtpCtrlPartitionOwnerSwCfg:
      *reg_offset = OTP_CTRL_OWNER_SW_CFG_READ_LOCK_REG_OFFSET;
      *index = OTP_CTRL_OWNER_SW_CFG_READ_LOCK_OWNER_SW_CFG_READ_LOCK_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_otp_ctrl_result_t dif_otp_ctrl_lock_reading(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  ptrdiff_t offset;
  bitfield_bit32_index_t index;
  if (!sw_read_lock_reg_offset(partition, &offset, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(otp->params.base_addr, offset, reg);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_reading_is_locked(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifOtpCtrlBadArg;
  }

  ptrdiff_t offset;
  bitfield_bit32_index_t index;
  if (!sw_read_lock_reg_offset(partition, &offset, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg = mmio_region_read32(otp->params.base_addr, offset);
  *is_locked = !bitfield_bit32_read(reg, index);
  return kDifOtpCtrlOk;
}

static bool irq_index(dif_otp_ctrl_irq_t irq, bitfield_bit32_index_t *index) {
  switch (irq) {
    case kDifOtpCtrlIrqDone:
      *index = OTP_CTRL_INTR_COMMON_OTP_OPERATION_DONE_BIT;
      break;
    case kDifOtpCtrlIrqError:
      *index = OTP_CTRL_INTR_COMMON_OTP_ERROR_BIT;
      break;
    default:
      return false;
  }
  return true;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_is_pending(const dif_otp_ctrl_t *otp,
                                                  dif_otp_ctrl_irq_t irq,
                                                  bool *is_pending) {
  if (otp == NULL || is_pending == NULL) {
    return kDifOtpCtrlBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg =
      mmio_region_read32(otp->params.base_addr, OTP_CTRL_INTR_STATE_REG_OFFSET);
  *is_pending = bitfield_bit32_read(reg, index);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_acknowledge(const dif_otp_ctrl_t *otp,
                                                   dif_otp_ctrl_irq_t irq) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_INTR_STATE_REG_OFFSET,
                      reg);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_get_enabled(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_irq_t irq,
    dif_otp_ctrl_toggle_t *state) {
  if (otp == NULL || state == NULL) {
    return kDifOtpCtrlBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg = mmio_region_read32(otp->params.base_addr,
                                    OTP_CTRL_INTR_ENABLE_REG_OFFSET);
  *state = bitfield_bit32_read(reg, index) ? kDifOtpCtrlToggleEnabled
                                           : kDifOtpCtrlToggleDisabled;

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_set_enabled(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_irq_t irq,
    dif_otp_ctrl_toggle_t state) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifOtpCtrlBadArg;
  }

  bool flag;
  switch (state) {
    case kDifOtpCtrlToggleEnabled:
      flag = true;
      break;
    case kDifOtpCtrlToggleDisabled:
      flag = false;
      break;
    default:
      return kDifOtpCtrlBadArg;
  }

  uint32_t reg = mmio_region_read32(otp->params.base_addr,
                                    OTP_CTRL_INTR_ENABLE_REG_OFFSET);
  reg = bitfield_bit32_write(reg, index, flag);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                      reg);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_force(const dif_otp_ctrl_t *otp,
                                             dif_otp_ctrl_irq_t irq) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  bitfield_bit32_index_t index;
  if (!irq_index(irq, &index)) {
    return kDifOtpCtrlBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, true);
  mmio_region_write32(otp->params.base_addr, OTP_CTRL_INTR_TEST_REG_OFFSET,
                      reg);

  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_disable_all(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_irq_snapshot_t *snapshot) {
  if (otp == NULL) {
    return kDifOtpCtrlBadArg;
  }

  if (snapshot != NULL) {
    *snapshot = mmio_region_read32(otp->params.base_addr,
                                   OTP_CTRL_INTR_ENABLE_REG_OFFSET);
  }

  mmio_region_write32(otp->params.base_addr, OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                      0);
  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_irq_restore_all(
    const dif_otp_ctrl_t *otp, const dif_otp_ctrl_irq_snapshot_t *snapshot) {
  if (otp == NULL || snapshot == NULL) {
    return kDifOtpCtrlBadArg;
  }

  mmio_region_write32(otp->params.base_addr, OTP_CTRL_INTR_ENABLE_REG_OFFSET,
                      *snapshot);
  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_get_status(const dif_otp_ctrl_t *otp,
                                              dif_otp_ctrl_status_t *status) {
  if (otp == NULL || status == NULL) {
    return kDifOtpCtrlBadArg;
  }

  static const bitfield_bit32_index_t kIndices[] = {
      [kDifOtpCtrlStatusCodeCreatorSwCfgError] =
          OTP_CTRL_STATUS_CREATOR_SW_CFG_ERROR_BIT,
      [kDifOtpCtrlStatusCodeOwnerSwCfgError] =
          OTP_CTRL_STATUS_OWNER_SW_CFG_ERROR_BIT,
      [kDifOtpCtrlStatusCodeHwCfgError] = OTP_CTRL_STATUS_HW_CFG_ERROR_BIT,
      [kDifOtpCtrlStatusCodeLifeCycleError] =
          OTP_CTRL_STATUS_LIFE_CYCLE_ERROR_BIT,
      [kDifOtpCtrlStatusCodeSecret0Error] = OTP_CTRL_STATUS_SECRET0_ERROR_BIT,
      [kDifOtpCtrlStatusCodeSecret1Error] = OTP_CTRL_STATUS_SECRET1_ERROR_BIT,
      [kDifOtpCtrlStatusCodeSecret2Error] = OTP_CTRL_STATUS_SECRET2_ERROR_BIT,
      [kDifOtpCtrlStatusCodeDaiError] = OTP_CTRL_STATUS_DAI_ERROR_BIT,
      [kDifOtpCtrlStatusCodeLciError] = OTP_CTRL_STATUS_LCI_ERROR_BIT,
      [kDifOtpCtrlStatusCodeTimeoutError] = OTP_CTRL_STATUS_TIMEOUT_ERROR_BIT,
      [kDifOtpCtrlStatusCodeLfsrError] = OTP_CTRL_STATUS_LFSR_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeScramblingError] =
          OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeKdfError] = OTP_CTRL_STATUS_KEY_DERIV_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeDaiIdle] = OTP_CTRL_STATUS_DAI_IDLE_BIT,
      [kDifOtpCtrlStatusCodeCheckPending] = OTP_CTRL_STATUS_CHECK_PENDING_BIT,
  };

  status->codes = 0;
  uint32_t status_code =
      mmio_region_read32(otp->params.base_addr, OTP_CTRL_STATUS_REG_OFFSET);
  uint32_t error_codes =
      mmio_region_read32(otp->params.base_addr, OTP_CTRL_ERR_CODE_REG_OFFSET);
  for (int i = 0; i < ARRAYSIZE(kIndices); ++i) {
    // If the error is not present at all, we clear its cause bit if relevant,
    // and bail immediately.
    if (!bitfield_bit32_read(status_code, kIndices[i])) {
      if (i <= kDifOtpCtrlStatusCodeHasCauseLast) {
        status->causes[i] = kDifOtpCtrlErrorOk;
      }
      continue;
    }

    status->codes = bitfield_bit32_write(status->codes, i, true);

    bitfield_field32_t field;
    switch (i) {
      case kDifOtpCtrlStatusCodeCreatorSwCfgError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_0_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_0_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeOwnerSwCfgError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_1_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_1_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeHwCfgError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_2_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_2_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeSecret0Error:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_3_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_3_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeSecret1Error:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_4_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_4_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeSecret2Error:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_5_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_5_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeLifeCycleError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_6_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_6_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeDaiError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_7_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_7_OFFSET,
        };
        break;
      case kDifOtpCtrlStatusCodeLciError:
        field = (bitfield_field32_t){
            .mask = OTP_CTRL_ERR_CODE_ERR_CODE_8_MASK,
            .index = OTP_CTRL_ERR_CODE_ERR_CODE_8_OFFSET,
        };
        break;
      // Not an error status, so there's nothing to do.
      default:
        continue;
    }

    dif_otp_ctrl_error_t err;
    switch (bitfield_field32_read(error_codes, field)) {
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_NO_ERROR:
        err = kDifOtpCtrlErrorOk;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_ERROR:
        err = kDifOtpCtrlErrorMacroUnspecified;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_ECC_CORR_ERROR:
        err = kDifOtpCtrlErrorMacroRecoverableRead;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_ECC_UNCORR_ERROR:
        err = kDifOtpCtrlErrorMacroUnrecoverableRead;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_MACRO_WRITE_BLANK_ERROR:
        err = kDifOtpCtrlErrorMacroBlankCheckFailed;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_ACCESS_ERROR:
        err = kDifOtpCtrlErrorLockedAccess;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_CHECK_FAIL_ERROR:
        err = kDifOtpCtrlErrorBackgroundCheckFailed;
        break;
      case OTP_CTRL_ERR_CODE_ERR_CODE_0_VALUE_FSM_STATE_ERROR:
        err = kDifOtpCtrlErrorFsmBadState;
        break;
      default:
        return kDifOtpCtrlError;
    }
    status->causes[i] = err;
  }

  return kDifOtpCtrlOk;
}

typedef struct partition_info {
  /**
   * The absolute OTP address at which this partition starts.
   */
  uint32_t start_addr;
  /**
   * The length of this partition, in bytes, including the digest.
   *
   * If the partition has a digest, it is expected to be at address
   * `start_addr + len - sizeof(uint64_t)`.
   */
  uint32_t len;
  /**
   * The alignment mask for this partition.
   *
   * A valid address for this partition must be such that
   * `addr & align_mask == 0`.
   */
  uint32_t align_mask;

  /**
   * Whether this is a software-managed partition with a software-managed
   * digest.
   */
  bool is_software;
} partition_info_t;

static const partition_info_t kPartitions[] = {
    // TODO: These should be provided by the gen'd header.
    // See #3904.
    [kDifOtpCtrlPartitionCreatorSwCfg] =
        {
            .start_addr = 0,
            .len = 0x300,
            .align_mask = 0x3,
            .is_software = true,
        },
    [kDifOtpCtrlPartitionOwnerSwCfg] =
        {
            .start_addr = 0x300,
            .len = 0x300,
            .align_mask = 0x3,
            .is_software = true,
        },
    [kDifOtpCtrlPartitionHwCfg] =
        {
            .start_addr = 0x600,
            .len = 0xb0,
            .align_mask = 0x3,
        },
    [kDifOtpCtrlPartitionSecret0] =
        {
            .start_addr = 0x6b0,
            .len = 0x28,
            .align_mask = 0x7,
        },
    [kDifOtpCtrlPartitionSecret1] =
        {
            .start_addr = 0x6d8,
            .len = 0x58,
            .align_mask = 0x7,
        },
    [kDifOtpCtrlPartitionSecret2] =
        {
            .start_addr = 0x730,
            .len = 0x58,
            .align_mask = 0x7,
        },
    [kDifOtpCtrlPartitionLifeCycle] =
        {
            .start_addr = 0x7a8,
            .len = 0x58,
            .align_mask = 0x3,
        },
};

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_read_start(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint32_t address) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifOtpCtrlDaiBadArg;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifOtpCtrlDaiUnaligned;
  }

  if (address >= kPartitions[partition].len) {
    return kDifOtpCtrlDaiOutOfRange;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, address);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);

  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_read32_end(const dif_otp_ctrl_t *otp,
                                                      uint32_t *value) {
  if (otp == NULL || value == NULL) {
    return kDifOtpCtrlDaiBadArg;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  *value = mmio_region_read32(otp->params.base_addr,
                              OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_read64_end(const dif_otp_ctrl_t *otp,
                                                      uint64_t *value) {
  if (otp == NULL || value == NULL) {
    return kDifOtpCtrlDaiBadArg;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  *value = mmio_region_read32(otp->params.base_addr,
                              OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET);
  *value <<= 32;
  *value |= mmio_region_read32(otp->params.base_addr,
                               OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_program32(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint32_t address, uint32_t value) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifOtpCtrlDaiBadArg;
  }

  // Ensure that we are writing to a 32-bit-access partition by checking that
  // the alignment mask is 0b11.
  //
  // Note furthermore that the LC partition is *not* writeable, so we eject
  // here.
  if (kPartitions[partition].align_mask != 0x3 ||
      partition == kDifOtpCtrlPartitionLifeCycle) {
    return kDifOtpCtrlDaiBadPartition;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifOtpCtrlDaiUnaligned;
  }

  // NOTE: The bounds check is tightened here, since we disallow writing the
  // digest directly.
  size_t digest_size = sizeof(uint64_t);
  if (address >= kPartitions[partition].len - digest_size) {
    return kDifOtpCtrlDaiOutOfRange;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, address);

  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET, value);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);

  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_program64(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint32_t address, uint64_t value) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifOtpCtrlDaiBadArg;
  }

  // Ensure that we are writing to a 32-bit-access partition by checking that
  // the alignment mask is 0b11.
  if (kPartitions[partition].align_mask != 0x7) {
    return kDifOtpCtrlDaiBadPartition;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifOtpCtrlDaiUnaligned;
  }

  // NOTE: The bounds check is tightened here, since we disallow writing the
  // digest directly.
  size_t digest_size = sizeof(uint64_t);
  if (address >= kPartitions[partition].len - digest_size) {
    return kDifOtpCtrlDaiOutOfRange;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, address);

  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
                      value & UINT32_MAX);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET, value >> 32);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);

  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_dai_digest(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint64_t digest) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifOtpCtrlDaiBadArg;
  }

  // The LC partition does not have a digest.
  if (partition == kDifOtpCtrlPartitionLifeCycle) {
    return kDifOtpCtrlDaiBadPartition;
  }

  // For software partitions, the digest must be nonzero; for all other
  // partitions it must be zero.
  bool is_sw = kPartitions[partition].is_software;
  if (is_sw == (digest == 0)) {
    return kDifOtpCtrlDaiBadArg;
  }

  uint32_t busy = mmio_region_read32(otp->params.base_addr,
                                     OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  if (!bitfield_bit32_read(
          busy, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT)) {
    return kDifOtpCtrlDaiBusy;
  }

  uint32_t address = kPartitions[partition].start_addr;
  if (is_sw) {
    address += kPartitions[partition].len - sizeof(digest);
  }
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET, address);

  if (digest != 0) {
    mmio_region_write32(otp->params.base_addr,
                        OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
                        digest & 0xffffffff);
    mmio_region_write32(otp->params.base_addr,
                        OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET,
                        digest >> 32);
  }

  bitfield_bit32_index_t cmd_bit = is_sw
                                       ? OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT
                                       : OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT;
  uint32_t cmd = bitfield_bit32_write(0, cmd_bit, true);
  mmio_region_write32(otp->params.base_addr,
                      OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET, cmd);

  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_digest_result_t dif_otp_ctrl_get_digest(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint64_t *digest) {
  if (otp == NULL || digest == NULL) {
    return kDifOtpCtrlDigestBadArg;
  }

  // The LC partition does not have a digest.
  if (partition == kDifOtpCtrlPartitionLifeCycle) {
    return kDifOtpCtrlDigestBadArg;
  }

  ptrdiff_t reg0, reg1;
  switch (partition) {
    case kDifOtpCtrlPartitionCreatorSwCfg:
      reg0 = OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_CREATOR_SW_CFG_DIGEST_1_REG_OFFSET;
      break;
    case kDifOtpCtrlPartitionOwnerSwCfg:
      reg0 = OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_OWNER_SW_CFG_DIGEST_1_REG_OFFSET;
      break;
    case kDifOtpCtrlPartitionHwCfg:
      reg0 = OTP_CTRL_HW_CFG_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_HW_CFG_DIGEST_1_REG_OFFSET;
      break;
    case kDifOtpCtrlPartitionSecret0:
      reg0 = OTP_CTRL_SECRET0_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_SECRET0_DIGEST_1_REG_OFFSET;
      break;
    case kDifOtpCtrlPartitionSecret1:
      reg0 = OTP_CTRL_SECRET1_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_SECRET1_DIGEST_1_REG_OFFSET;
      break;
    case kDifOtpCtrlPartitionSecret2:
      reg0 = OTP_CTRL_SECRET2_DIGEST_0_REG_OFFSET;
      reg1 = OTP_CTRL_SECRET2_DIGEST_1_REG_OFFSET;
      break;
    default:
      return kDifOtpCtrlDigestBadArg;
  }

  uint64_t value = mmio_region_read32(otp->params.base_addr, reg1);
  value <<= 32;
  value |= mmio_region_read32(otp->params.base_addr, reg0);

  if (value == 0) {
    return kDifOtpCtrlDigestMissing;
  }
  *digest = value;

  return kDifOtpCtrlDigestOk;
}

dif_otp_ctrl_dai_result_t dif_otp_ctrl_read_blocking(
    const dif_otp_ctrl_t *otp, dif_otp_ctrl_partition_t partition,
    uint32_t address, uint32_t *buf, size_t len) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions) || buf == NULL) {
    return kDifOtpCtrlDaiBadArg;
  }

  if (!kPartitions[partition].is_software) {
    return kDifOtpCtrlDaiBadPartition;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifOtpCtrlDaiUnaligned;
  }

  if (address + len >= kPartitions[partition].len) {
    return kDifOtpCtrlDaiOutOfRange;
  }

  ptrdiff_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                         kPartitions[partition].start_addr + address;
  mmio_region_memcpy_from_mmio32(otp->params.base_addr, reg_offset, buf,
                                 len * sizeof(uint32_t));
  return kDifOtpCtrlDaiOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_read_test(const dif_otp_ctrl_t *otp,
                                             uint32_t address, uint32_t *buf,
                                             size_t len) {
  if (otp == NULL || buf == NULL) {
    return kDifOtpCtrlBadArg;
  }

  ptrdiff_t reg_offset = OTP_CTRL_TEST_ACCESS_REG_OFFSET + address;
  mmio_region_memcpy_from_mmio32(otp->params.base_addr, reg_offset, buf,
                                 len * sizeof(uint32_t));
  return kDifOtpCtrlOk;
}

dif_otp_ctrl_result_t dif_otp_ctrl_write_test(const dif_otp_ctrl_t *otp,
                                              uint32_t address,
                                              const uint32_t *buf, size_t len) {
  if (otp == NULL || buf == NULL) {
    return kDifOtpCtrlBadArg;
  }

  ptrdiff_t reg_offset = OTP_CTRL_TEST_ACCESS_REG_OFFSET + address;
  mmio_region_memcpy_to_mmio32(otp->params.base_addr, reg_offset, buf,
                               len * sizeof(uint32_t));
  return kDifOtpCtrlOk;
}
