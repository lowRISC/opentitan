// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_LZ4_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_LZ4_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Decompresses a raw LZ4 block into a destination buffer.
 *
 * This implementation is designed specifically for constrained embedded
 * environments. It performs no dynamic allocation and requires no
 * framing metadata.
 *
 * @param src Pointer to the compressed data.
 * @param dst Pointer to the destination buffer.
 * @param compressed_size The exact size of the compressed data.
 * @param dst_capacity The maximum capacity of the destination buffer.
 * @return The number of bytes decompressed, or a negative value on error.
 */
int LZ4_decompress(const char *src, char *dst, int compressed_size,
                   int dst_capacity);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_LZ4_H_
