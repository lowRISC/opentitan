// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

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
  kOtpSecMmioCreatorSwCfgLockDown = 1,
};

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
