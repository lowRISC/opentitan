// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "otp_ctrl_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions provided by this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  otp_creator_sw_cfg_lockdown();
 *  SEC_MMIO_WRITE_INCREMENT(kOtpSecMmioCreatorSwCfgLockDown);
 * ```
 */
enum {
  /**
   * Individual register reads/writes.
   */
  kOtpSecMmioCreatorSwCfgLockDown = 1,
};

/**
 * OTP partition information.
 */
typedef struct otp_partition_info {
  /**
   * The absolute OTP address at which this partition starts.
   */
  uint32_t start_addr;
  /**
   * Size (in bytes) of the partition, excluding the digest field.
   */
  size_t size;
  /**
   * The absolute OTP address at which this partition's digest starts.
   */
  uint32_t digest_addr;
  /**
   * The alignment mask for this partition.
   *
   * A valid address for this partition must be such that
   * `addr & align_mask == 0`.
   */
  uint32_t align_mask;
} otp_partition_info_t;

/**
 * OTP partitions whose fields are readable after being locked.
 */
typedef enum otp_partition {
  kOtpPartitionCreatorSwCfg = 0,
  kOtpPartitionOwnerSwCfg = 1,
  kOtpPartitionRotCreatorAuthCodesign = 2,
  kOtpPartitionRotCreatorAuthState = 3,
  kOtpPartitionHwCfg0 = 4,
  kOtpPartitionHwCfg1 = 5,
  kOtpPartitionNumPartitions = 6,
} otp_partition_t;

/**
 * Table of OTP partition information.
 */
extern const otp_partition_info_t kOtpPartitions[];

/**
 * Perform a blocking 32-bit read from the memory mapped software config
 * partitions.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 32-bit value from OTP.
 */
OT_WARN_UNUSED_RESULT
uint32_t otp_read32(uint32_t address);

/**
 * Perform a blocking 64-bit read from the memory mapped software config
 * partitions.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 64-bit value from OTP.
 */
OT_WARN_UNUSED_RESULT
uint64_t otp_read64(uint32_t address);

/**
 * Perform a blocking read of `num_words` 32-bit words from the memory mapped
 * software config partitions.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @param data The output buffer of at least length `num_words`.
 * @param num_words The number of 32-bit words to read from OTP.
 */
void otp_read(uint32_t address, uint32_t *data, size_t num_words);

/**
 * Read a partition's 64-bit digest from the corresponding CSRs.
 *
 * @param partition The OTP partition whose digest should be read.
 * @return The 64-bit digest value.
 */
uint64_t otp_partition_digest_read(otp_partition_t partition);

/**
 * Perform a blocking 32-bit read from the Direct Access Interface (DAI).
 *
 * This enables reading any readable 32-bit OTP field that is not in the memory
 * mapped software config partitions (i.e., partitions other than the
 * {CREATOR,OWNER}_SW_CFG partitions).
 *
 * @param partition The OTP partition to read from.
 * @param relative_address The address to read from, relative to the start of
 *                         the OTP partition.
 * @return The 32-bit value from OTP.
 */
uint32_t otp_dai_read32(otp_partition_t partition, uint32_t address);

/**
 * Perform a blocking 64-bit read from the Direct Access Interface (DAI).
 *
 * This enables reading any readable 64-bit OTP field that is not in the memory
 * mapped software config partitions (i.e., partitions other than the
 * {CREATOR,OWNER}_SW_CFG partitions).
 *
 * @param partition The OTP partition to read from.
 * @param relative_address The address to read from, relative to the start of
 *                         the OTP partition.
 * @return The 64-bit value from OTP.
 */
uint64_t otp_dai_read64(otp_partition_t partition, uint32_t address);

/**
 * Perform a blocking read of `num_words` 32-bit words from the Direct Access
 * Interface (DAI).
 *
 * Note: this should only be used to read 32-bit granule OTP regions.
 *
 * @param partition The OTP partition to read from.
 * @param relative_address The address to read from, relative to the start of
 *                         the OTP partition.
 * @param data The output buffer of at least length `num_words`.
 * @param num_words The number of 32-bit words to read from OTP.
 */
rom_error_t otp_dai_read(otp_partition_t partition, uint32_t address,
                         uint32_t *data, size_t num_words);

/**
 * Disables read access to CREATOR_SW_CFG partition until next reset.
 *
 * This function must be called in ROM_EXT before handing over execution to the
 * first owner boot stage.
 */
void otp_creator_sw_cfg_lockdown(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
