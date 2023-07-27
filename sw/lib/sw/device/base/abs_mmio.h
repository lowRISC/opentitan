// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_ABS_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_ABS_MMIO_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @file
 * @brief Absolute Memory-mapped IO functions, for volatile access.
 *
 * Memory-mapped IO functions, which map to volatile accesses. Use this module
 * for register operations in ROM and ROM Extension production libraries.
 *
 * Compiling translation units that pull in this header with `-DMOCK_ABS_MMIO`
 * will disable the definitions of `abs_mmio_read` and `abs_mmio_write`. These
 * symbols can then be defined by a test harness to allow for instrumentation of
 * MMIO accesses.
 */

#ifdef OT_PLATFORM_RV32

/**
 * Reads uint8_t from MMIO `addr`.
 *
 * @param addr the address to read from.
 * @return the read value.
 */
OT_WARN_UNUSED_RESULT
inline uint8_t abs_mmio_read8(uint32_t addr) {
  return *((volatile uint8_t *)addr);
}

/**
 * Writes uint8_t to the MMIO `addr`.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
inline void abs_mmio_write8(uint32_t addr, uint8_t value) {
  *((volatile uint8_t *)addr) = value;
}

/**
 * Writes uint8_t to the MMIO `addr` via
 * two subsequent write operations.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
inline void abs_mmio_write8_shadowed(uint32_t addr, uint8_t value) {
  *((volatile uint8_t *)addr) = value;
  *((volatile uint8_t *)addr) = value;
}

/**
 * Reads an aligned uint32_t from MMIO `addr`.
 *
 * @param addr the address to read from.
 * @return the read value.
 */
OT_WARN_UNUSED_RESULT
inline uint32_t abs_mmio_read32(uint32_t addr) {
  return *((volatile uint32_t *)addr);
}

/**
 * Writes an aligned uint32_t to the MMIO `addr`.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
inline void abs_mmio_write32(uint32_t addr, uint32_t value) {
  *((volatile uint32_t *)addr) = value;
}

/**
 * Writes an aligned uint32_t to the MMIO `addr` via
 * two subsequent write operations.
 *
 * @param addr the address to write to.
 * @param value the value to write.
 */
inline void abs_mmio_write32_shadowed(uint32_t addr, uint32_t value) {
  *((volatile uint32_t *)addr) = value;
  *((volatile uint32_t *)addr) = value;
}

#else  // OT_PLATFORM_RV32

extern uint8_t abs_mmio_read8(uint32_t addr);
extern void abs_mmio_write8(uint32_t addr, uint8_t value);
extern void abs_mmio_write8_shadowed(uint32_t addr, uint8_t value);
extern uint32_t abs_mmio_read32(uint32_t addr);
extern void abs_mmio_write32(uint32_t addr, uint32_t value);
extern void abs_mmio_write32_shadowed(uint32_t addr, uint32_t value);

#endif  // OT_PLATFORM_RV32

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_ABS_MMIO_H_
