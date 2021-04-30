// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MMIO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MMIO_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * All MMIO functions return their results using return values, rather than out-
 * parameters. Where the return types are non-void, it is prudent to ensure
 * these results are used, or explicitly discarded (in the case of a volatile
 * read that is needed for side effects only).
 */
#define MMIO_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

MMIO_WARN_UNUSED_RESULT
uint32_t rom_mmio_read8(uint32_t addr);

/**
 * Writes an aligned uint8_t to the MMIO region `addr`.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
void rom_mmio_write8(uint32_t addr, uint32_t value);

MMIO_WARN_UNUSED_RESULT
uint32_t rom_mmio_read32(uint32_t addr);

/**
 * Writes an aligned uint32_t to the MMIO region `addr`.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
void rom_mmio_write32(uint32_t addr, uint32_t value);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BASE_MMIO_H_
