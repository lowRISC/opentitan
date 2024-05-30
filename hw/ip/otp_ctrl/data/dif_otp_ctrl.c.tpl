// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_comment}
<%
from topgen.lib import Name

parts = otp_mmap.config["partitions"]
digest_parts = [part for part in parts if
                part["hw_digest"] or part["sw_digest"]]
read_locked_csr_parts = [part for part in parts if part["read_lock"] == "CSR"]
secret_parts = [part for part in parts if part["secret"]]
%>\
#include "sw/device/lib/dif/dif_otp_ctrl.h"

#include <stddef.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_base.h"

#include "otp_ctrl_regs.h"  // Generated.

/**
 * Checks if integrity/consistency-check-related operations are locked.
 *
 * This is a convenience function to avoid superfluous error-checking in all the
 * functions that can be locked out by this register.
 *
 * @param check_config True to check the config regwen. False to check the
 * trigger regwen.
 */
static bool checks_are_locked(const dif_otp_ctrl_t *otp, bool check_config) {
  ptrdiff_t reg_offset = check_config
                             ? OTP_CTRL_CHECK_REGWEN_REG_OFFSET
                             : OTP_CTRL_CHECK_TRIGGER_REGWEN_REG_OFFSET;
  size_t regwen_bit =
      check_config ? OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT
                   : OTP_CTRL_CHECK_TRIGGER_REGWEN_CHECK_TRIGGER_REGWEN_BIT;
  uint32_t locked = mmio_region_read32(otp->base_addr, reg_offset);
  return !bitfield_bit32_read(locked, regwen_bit);
}

dif_result_t dif_otp_ctrl_configure(const dif_otp_ctrl_t *otp,
                                    dif_otp_ctrl_config_t config) {
  if (otp == NULL) {
    return kDifBadArg;
  }
  if (checks_are_locked(otp, /*check_config=*/true)) {
    return kDifLocked;
  }

  mmio_region_write32(otp->base_addr, OTP_CTRL_CHECK_TIMEOUT_REG_OFFSET,
                      config.check_timeout);
  mmio_region_write32(otp->base_addr,
                      OTP_CTRL_INTEGRITY_CHECK_PERIOD_REG_OFFSET,
                      config.integrity_period_mask);
  mmio_region_write32(otp->base_addr,
                      OTP_CTRL_CONSISTENCY_CHECK_PERIOD_REG_OFFSET,
                      config.consistency_period_mask);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_check_integrity(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifBadArg;
  }
  if (checks_are_locked(otp, /*check_config=*/false)) {
    return kDifLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_TRIGGER_INTEGRITY_BIT, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_CHECK_TRIGGER_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_check_consistency(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifBadArg;
  }
  if (checks_are_locked(otp, /*check_config=*/false)) {
    return kDifLocked;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_TRIGGER_CONSISTENCY_BIT, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_CHECK_TRIGGER_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_lock(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      0, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT, false);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET,
                      reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_is_locked(const dif_otp_ctrl_t *otp,
                                        bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(otp->base_addr,
                                    OTP_CTRL_DIRECT_ACCESS_REGWEN_REG_OFFSET);
  *is_locked = !bitfield_bit32_read(
      reg, OTP_CTRL_DIRECT_ACCESS_REGWEN_DIRECT_ACCESS_REGWEN_BIT);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_lock_config(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      bitfield_bit32_write(0, OTP_CTRL_CHECK_REGWEN_CHECK_REGWEN_BIT, false);
  mmio_region_write32(otp->base_addr, OTP_CTRL_CHECK_REGWEN_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_config_is_locked(const dif_otp_ctrl_t *otp,
                                           bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = checks_are_locked(otp, /*check_config=*/true);
  return kDifOk;
}

dif_result_t dif_otp_ctrl_lock_check_trigger(const dif_otp_ctrl_t *otp) {
  if (otp == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(
      0, OTP_CTRL_CHECK_TRIGGER_REGWEN_CHECK_TRIGGER_REGWEN_BIT, false);
  mmio_region_write32(otp->base_addr, OTP_CTRL_CHECK_TRIGGER_REGWEN_REG_OFFSET,
                      reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_check_trigger_is_locked(const dif_otp_ctrl_t *otp,
                                                  bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = checks_are_locked(otp, /*check_config=*/false);
  return kDifOk;
}

static bool sw_read_lock_reg_offset(dif_otp_ctrl_partition_t partition,
                                    ptrdiff_t *reg_offset,
                                    bitfield_bit32_index_t *index) {
  switch (partition) {
% for part in read_locked_csr_parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_define = part_name.as_c_define()
  index_line = f"*index = OTP_CTRL_{part_name_define}_READ_LOCK_{part_name_define}_READ_LOCK_BIT;"
%>\
    case kDifOtpCtrlPartition${part_name.as_camel_case()}:
      *reg_offset = OTP_CTRL_${part_name_define}_READ_LOCK_REG_OFFSET;
  % if len(index_line) > 80 - 6:
      *index =
          OTP_CTRL_${part_name_define}_READ_LOCK_${part_name_define}_READ_LOCK_BIT;
  % else:
      ${index_line}
  % endif
      break;
% endfor
    default:
      return false;
  }
  return true;
}

dif_result_t dif_otp_ctrl_lock_reading(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition) {
  if (otp == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t offset;
  bitfield_bit32_index_t index;
  if (!sw_read_lock_reg_offset(partition, &offset, &index)) {
    return kDifBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, index, false);
  mmio_region_write32(otp->base_addr, offset, reg);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_reading_is_locked(const dif_otp_ctrl_t *otp,
                                            dif_otp_ctrl_partition_t partition,
                                            bool *is_locked) {
  if (otp == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t offset;
  bitfield_bit32_index_t index;
  if (!sw_read_lock_reg_offset(partition, &offset, &index)) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(otp->base_addr, offset);
  *is_locked = !bitfield_bit32_read(reg, index);
  return kDifOk;
}

dif_result_t dif_otp_ctrl_get_status(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_status_t *status) {
  if (otp == NULL || status == NULL) {
    return kDifBadArg;
  }

  static const bitfield_bit32_index_t kIndices[] = {
% for part in parts:
<%
  part_name = Name.from_snake_case(part["name"])
  lhs = f'[kDifOtpCtrlStatusCode{part_name.as_camel_case()}Error]'
  rhs = f'OTP_CTRL_STATUS_{part_name.as_c_define()}_ERROR_BIT'
  line = f'{lhs} = {rhs},'
%>\
  % if len(line) > 80 - 6:
      ${lhs} =
          ${rhs},
  % else:
      ${line}
  % endif
% endfor
      [kDifOtpCtrlStatusCodeDaiError] = OTP_CTRL_STATUS_DAI_ERROR_BIT,
      [kDifOtpCtrlStatusCodeLciError] = OTP_CTRL_STATUS_LCI_ERROR_BIT,
      [kDifOtpCtrlStatusCodeTimeoutError] = OTP_CTRL_STATUS_TIMEOUT_ERROR_BIT,
      [kDifOtpCtrlStatusCodeLfsrError] = OTP_CTRL_STATUS_LFSR_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeScramblingError] =
          OTP_CTRL_STATUS_SCRAMBLING_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeKdfError] = OTP_CTRL_STATUS_KEY_DERIV_FSM_ERROR_BIT,
      [kDifOtpCtrlStatusCodeBusIntegError] =
          OTP_CTRL_STATUS_BUS_INTEG_ERROR_BIT,
      [kDifOtpCtrlStatusCodeDaiIdle] = OTP_CTRL_STATUS_DAI_IDLE_BIT,
      [kDifOtpCtrlStatusCodeCheckPending] = OTP_CTRL_STATUS_CHECK_PENDING_BIT,
  };

  status->codes = 0;
  uint32_t status_code =
      mmio_region_read32(otp->base_addr, OTP_CTRL_STATUS_REG_OFFSET);
  for (int i = 0; i < ARRAYSIZE(kIndices); ++i) {
    // If the error is not present at all, we clear its cause bit if relevant,
    // and bail immediately.
    if (!bitfield_bit32_read(status_code, kIndices[i])) {
      if (i <= kDifOtpCtrlStatusCodeHasCauseLast) {
        status->causes[i] = kDifOtpCtrlErrorOk;
      }
      continue;
    }

    status->codes =
        bitfield_bit32_write(status->codes, (bitfield_bit32_index_t)i, true);

    if (i <= kDifOtpCtrlStatusCodeHasCauseLast) {
      bitfield_field32_t field;
      field = (bitfield_field32_t){
          .mask = OTP_CTRL_ERR_CODE_0_ERR_CODE_0_MASK,
          .index = OTP_CTRL_ERR_CODE_0_ERR_CODE_0_OFFSET,
      };

      ptrdiff_t address =
          OTP_CTRL_ERR_CODE_0_REG_OFFSET + i * (ptrdiff_t)sizeof(uint32_t);
      uint32_t error_code = mmio_region_read32(otp->base_addr, address);

      dif_otp_ctrl_error_t err;
      switch (bitfield_field32_read(error_code, field)) {
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_NO_ERROR:
          err = kDifOtpCtrlErrorOk;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_MACRO_ERROR:
          err = kDifOtpCtrlErrorMacroUnspecified;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_MACRO_ECC_CORR_ERROR:
          err = kDifOtpCtrlErrorMacroRecoverableRead;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_MACRO_ECC_UNCORR_ERROR:
          err = kDifOtpCtrlErrorMacroUnrecoverableRead;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_MACRO_WRITE_BLANK_ERROR:
          err = kDifOtpCtrlErrorMacroBlankCheckFailed;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_ACCESS_ERROR:
          err = kDifOtpCtrlErrorLockedAccess;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_CHECK_FAIL_ERROR:
          err = kDifOtpCtrlErrorBackgroundCheckFailed;
          break;
        case OTP_CTRL_ERR_CODE_0_ERR_CODE_0_VALUE_FSM_STATE_ERROR:
          err = kDifOtpCtrlErrorFsmBadState;
          break;
        default:
          return kDifError;
      }
      status->causes[i] = err;
    }
  }

  return kDifOk;
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

  /**
   * Whether this partition has a digest field.
   */
  bool has_digest;

  /**
   * Whether this partition is the lifecycle partition.
   */
  bool is_lifecycle;
} partition_info_t;

// This is generates too many lines with different formatting variants, so
// We opt to just disable formatting.
// clang-format off
static const partition_info_t kPartitions[] = {
% for part in parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
  part_name_define = part_name.as_c_define()
  has_digest = part["hw_digest"] or part["sw_digest"]
  is_lifecycle = part["variant"] == "LifeCycle"
  is_software = part["variant"] == "Unbuffered"
%>\
    [kDifOtpCtrlPartition${part_name_camel}] = {
        .start_addr = OTP_CTRL_PARAM_${part_name_define}_OFFSET,
        .len = OTP_CTRL_PARAM_${part_name_define}_SIZE,
        .align_mask = ${"0x7" if part in secret_parts else "0x3"},
        .is_software = ${"true" if is_software else "false"},
        .has_digest = ${"true" if has_digest else "false"},
        .is_lifecycle = ${"true" if is_lifecycle else "false"}},
% endfor
};
// clang-format on

dif_result_t dif_otp_ctrl_relative_address(dif_otp_ctrl_partition_t partition,
                                           uint32_t abs_address,
                                           uint32_t *relative_address) {
  *relative_address = 0;

  if (partition >= ARRAYSIZE(kPartitions)) {
    return kDifBadArg;
  }

  if ((abs_address & kPartitions[partition].align_mask) != 0) {
    return kDifUnaligned;
  }

  if (abs_address < kPartitions[partition].start_addr) {
    return kDifOutOfRange;
  }

  *relative_address = abs_address - kPartitions[partition].start_addr;
  if (*relative_address >= kPartitions[partition].len) {
    *relative_address = 0;
    return kDifOutOfRange;
  }

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_read_start(const dif_otp_ctrl_t *otp,
                                         dif_otp_ctrl_partition_t partition,
                                         uint32_t address) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifBadArg;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifUnaligned;
  }

  if (address >= kPartitions[partition].len) {
    return kDifOutOfRange;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                      address);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_RD_BIT, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                      cmd);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_read32_end(const dif_otp_ctrl_t *otp,
                                         uint32_t *value) {
  if (otp == NULL || value == NULL) {
    return kDifBadArg;
  }

  *value = mmio_region_read32(otp->base_addr,
                              OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_read64_end(const dif_otp_ctrl_t *otp,
                                         uint64_t *value) {
  if (otp == NULL || value == NULL) {
    return kDifBadArg;
  }

  *value = mmio_region_read32(otp->base_addr,
                              OTP_CTRL_DIRECT_ACCESS_RDATA_1_REG_OFFSET);
  *value <<= 32;
  *value |= mmio_region_read32(otp->base_addr,
                               OTP_CTRL_DIRECT_ACCESS_RDATA_0_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_program32(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint32_t value) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifBadArg;
  }

  // Ensure that we are writing to a 32-bit-access partition by checking that
  // the alignment mask is 0b11.
  //
  // Note furthermore that the LC partition is *not* writeable, so we eject
  // here.
  if (kPartitions[partition].align_mask != 0x3 ||
      kPartitions[partition].is_lifecycle) {
    return kDifError;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifUnaligned;
  }

  // NOTE: The bounds check is tightened here, since we disallow writing the
  // digest directly. If the partition does not have a digest, no tightening is
  // needed.
  size_t digest_size = kPartitions[partition].has_digest * sizeof(uint64_t);
  if (address >= kPartitions[partition].len - digest_size) {
    return kDifOutOfRange;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                      address);

  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
                      value);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                      cmd);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_program64(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint64_t value) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifBadArg;
  }

  // Ensure that we are writing to a 64-bit-access partition by checking that
  // the alignment mask is 0b111.
  if (kPartitions[partition].align_mask != 0x7) {
    return kDifError;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifUnaligned;
  }

  // NOTE: The bounds check is tightened here, since we disallow writing the
  // digest directly.
  size_t digest_size = sizeof(uint64_t);
  if (address >= kPartitions[partition].len - digest_size) {
    return kDifOutOfRange;
  }

  address += kPartitions[partition].start_addr;
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                      address);

  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
                      value & UINT32_MAX);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET,
                      value >> 32);

  uint32_t cmd =
      bitfield_bit32_write(0, OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                      cmd);

  return kDifOk;
}

dif_result_t dif_otp_ctrl_dai_digest(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_partition_t partition,
                                     uint64_t digest) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions)) {
    return kDifBadArg;
  }

  // Not all partitions have a digest.
  if (!kPartitions[partition].has_digest) {
    return kDifError;
  }

  // For software partitions, the digest must be nonzero; for all other
  // partitions it must be zero.
  bool is_sw = kPartitions[partition].is_software;
  if (is_sw == (digest == 0)) {
    return kDifBadArg;
  }

  uint32_t address = kPartitions[partition].start_addr;
  if (is_sw) {
    address += kPartitions[partition].len - sizeof(digest);
  }
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_ADDRESS_REG_OFFSET,
                      address);

  if (digest != 0) {
    mmio_region_write32(otp->base_addr,
                        OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
                        digest & 0xffffffff);
    mmio_region_write32(otp->base_addr,
                        OTP_CTRL_DIRECT_ACCESS_WDATA_1_REG_OFFSET,
                        digest >> 32);
  }

  bitfield_bit32_index_t cmd_bit = is_sw
                                       ? OTP_CTRL_DIRECT_ACCESS_CMD_WR_BIT
                                       : OTP_CTRL_DIRECT_ACCESS_CMD_DIGEST_BIT;
  uint32_t cmd = bitfield_bit32_write(0, cmd_bit, true);
  mmio_region_write32(otp->base_addr, OTP_CTRL_DIRECT_ACCESS_CMD_REG_OFFSET,
                      cmd);

  return kDifOk;
}

static bool get_digest_regs(dif_otp_ctrl_partition_t partition, ptrdiff_t *reg0,
                            ptrdiff_t *reg1) {
  switch (partition) {
% for part in digest_parts:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_define = part_name.as_c_define()
%>\
    case kDifOtpCtrlPartition${part_name.as_camel_case()}:
      *reg0 = OTP_CTRL_${part_name_define}_DIGEST_0_REG_OFFSET;
      *reg1 = OTP_CTRL_${part_name_define}_DIGEST_1_REG_OFFSET;
      break;
% endfor
    default:
      return false;
  }

  return true;
}

dif_result_t dif_otp_ctrl_is_digest_computed(const dif_otp_ctrl_t *otp,
                                             dif_otp_ctrl_partition_t partition,
                                             bool *is_computed) {
  if (otp == NULL || is_computed == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg0, reg1;
  if (!get_digest_regs(partition, &reg0, &reg1)) {
    return kDifBadArg;
  }

  uint64_t value = mmio_region_read32(otp->base_addr, reg1);
  value <<= 32;
  value |= mmio_region_read32(otp->base_addr, reg0);

  *is_computed = value != 0;

  return kDifOk;
}

dif_result_t dif_otp_ctrl_get_digest(const dif_otp_ctrl_t *otp,
                                     dif_otp_ctrl_partition_t partition,
                                     uint64_t *digest) {
  if (otp == NULL || digest == NULL) {
    return kDifBadArg;
  }

  ptrdiff_t reg0, reg1;
  if (!get_digest_regs(partition, &reg0, &reg1)) {
    return kDifBadArg;
  }

  uint64_t value = mmio_region_read32(otp->base_addr, reg1);
  value <<= 32;
  value |= mmio_region_read32(otp->base_addr, reg0);

  if (value == 0) {
    return kDifError;
  }
  *digest = value;

  return kDifOk;
}

dif_result_t dif_otp_ctrl_read_blocking(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t address, uint32_t *buf,
                                        size_t len) {
  if (otp == NULL || partition >= ARRAYSIZE(kPartitions) || buf == NULL) {
    return kDifBadArg;
  }

  if (!kPartitions[partition].is_software) {
    return kDifError;
  }

  if ((address & kPartitions[partition].align_mask) != 0) {
    return kDifUnaligned;
  }

  if (address + len >= kPartitions[partition].len) {
    return kDifOutOfRange;
  }

  uint32_t reg_offset = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                        kPartitions[partition].start_addr + address;
  mmio_region_memcpy_from_mmio32(otp->base_addr, reg_offset, buf,
                                 len * sizeof(uint32_t));
  return kDifOk;
}
