// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_HEXSTR_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_HEXSTR_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Encode binary data as a hexadecimal string.
 *
 * @param dst The destination string buffer.
 * @param dst_size The maximum size of the destination buffer (including the nul
 *                 terminator).
 * @param src The source data to encode.
 * @param src_size The size of the source data.
 * @return status_t Success or error code.
 */
status_t hexstr_encode(char *dst, size_t dst_size, const void *src,
                       size_t src_size);

/**
 * Decode binary data from a hexadecimal string.
 *
 * @param dst The destination binary buffer.
 * @param dst_size The size of the destination buffer.
 * @param src The source string to decode.
 * @return status_t Success or error code.
 */
status_t hexstr_decode(void *dst, size_t dst_size, const char *src);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_HEXSTR_H_
