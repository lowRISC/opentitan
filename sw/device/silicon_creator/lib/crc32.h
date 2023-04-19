// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRC32_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRC32_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Initializes the context variable for a CRC32 computation.
 *
 * @param[out] ctx Context variable.
 */
void crc32_init(uint32_t *ctx);

/**
 * Adds a byte to a CRC32.
 *
 * @param[in, out] ctx Context variable.
 * @param byte Byte to be added.
 */
void crc32_add8(uint32_t *ctx, uint8_t byte);

/**
 * Adds a word to a CRC32.
 *
 * @param[in, out] ctx Context variable.
 * @param word Word to be added.
 */
void crc32_add32(uint32_t *ctx, uint32_t word);

/**
 * Adds a buffer to a CRC32.
 *
 * @param[in, out] ctx Context variable.
 * @param buf A buffer, little-endian.
 * @param len Size of the buffer.
 */
void crc32_add(uint32_t *ctx, const void *buf, size_t len);

/**
 * Finishes a CRC32 computation.
 *
 * This function does not modify the context variable `ctx`.
 *
 * @param ctx Context variable.
 * @return Result of the computation.
 */
uint32_t crc32_finish(const uint32_t *ctx);

/**
 * Computes the CRC32 of a buffer as defined by IEEE 802.3 CRC-32. It also
 * matches Python's `zlib.crc32()`.
 *
 * @param buf A buffer, little-endian.
 * @param len Size of the buffer.
 * @return CRC32 of the buffer.
 */
uint32_t crc32(const void *buf, size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CRC32_H_
