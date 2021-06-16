// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

#define OTP_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

/**
 * Perform a blocking 32-bit read from the memory mapped software config
 * partitions.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 32-bit value from OTP.
 */
OTP_WARN_UNUSED_RESULT
uint32_t otp_read32(uint32_t address);

/**
 * Perform a blocking 64-bit read from the memory mapped software config
 * partitions.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 64-bit value from OTP.
 */
OTP_WARN_UNUSED_RESULT
uint64_t otp_read64(uint32_t address);

/**
 * Perform a blocking read of `len` bytes from the memory mapped software config
 * partitions. It is required that both `address` and `address` + `len` be
 * word-aligned.
 *
 * @param address The address to read from offset from the start of OTP memory.
 * @param data The output buffer of at least length `len`.
 * @param len The number of bytes to read from OTP.
 * @return `kErrorOtpBadAlignment` if `address` or `address` + `len` are
 * misaligned, `kErrorOk` otherwise.
 */
OTP_WARN_UNUSED_RESULT
rom_error_t otp_read(uint32_t address, void *data, size_t len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
