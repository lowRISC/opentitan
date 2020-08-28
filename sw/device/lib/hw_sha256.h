// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_HW_SHA256_H_
#define OPENTITAN_SW_DEVICE_LIB_HW_SHA256_H_

#include <stddef.h>

#include "sw/vendor/cryptoc/include/cryptoc/hash-internal.h"

typedef HASH_CTX HW_SHA256_CTX;

#define SHA256_DIGEST_SIZE 32

/**
 * hw_SHA256_init initializes `ctx`.
 *
 * @param ctx SHA256 context.
 */
void hw_SHA256_init(HW_SHA256_CTX *ctx);

/**
 * hw_SHA256_update adds `len` bytes from `data` to `ctx`.
 *
 * @param ctx SHA256 context.
 * @param data Input buffer.
 * @param len Number of bytes to add.
 */
void hw_SHA256_update(HW_SHA256_CTX *ctx, const void *data, size_t len);

/**
 * hw_SHA256_final adds the final padding to `ctx` and calculates digest.
 *
 * @param ctx SHA256 context.
 *
 * @return pointer to digest buffer held in `ctx`.
 */
const uint8_t *hw_SHA256_final(HW_SHA256_CTX *ctx);

/**
 * hw_SHA256_hash writes `digest` from `len` bytes of `data`.
 *
 * @param data Input buffer.
 * @param len Number of bytes to add.
 * @param[out] digest Output buffer.
 */
const uint8_t *hw_SHA256_hash(const void *data, size_t len, uint8_t *digest);

#endif  // OPENTITAN_SW_DEVICE_LIB_HW_SHA256_H_
