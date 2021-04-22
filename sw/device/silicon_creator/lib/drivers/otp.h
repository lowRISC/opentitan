// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct otp {
  /**
   * The base address for the OTP hardware registers.
   */
  mmio_region_t base_addr;
} otp_t;

/**
 * Perform a blocking 32-bit read from the memory mapped software config
 * partitions.
 *
 * @param otp The handle to the otp_ctrl device.
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 32-bit value from OTP.
 */
uint32_t otp_read32(const otp_t *otp, uint32_t address);

/**
 * Perform a blocking 64-bit read from the memory mapped software config
 * partitions.
 *
 * @param otp The handle to the otp_ctrl device.
 * @param address The address to read from offset from the start of OTP memory.
 * @return The 64-bit value from OTP.
 */
uint64_t otp_read64(const otp_t *otp, uint32_t address);

/**
 * Perform a blocking read of `len` bytes from the memory mapped software config
 * partitions.
 *
 * @param otp The handle to the otp_ctrl device.
 * @param address The address to read from offset from the start of OTP memory.
 * @param data The output buffer of at least length `len`.
 * @param len The number of bytes to read from OTP.
 */
void otp_read(const otp_t *otp, uint32_t address, void *data, size_t len);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTP_H_
