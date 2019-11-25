// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_LIB_HMAC_H__
#define _F_LIB_HMAC_H__

#include "sw/device/lib/base/types.h"

/**
 * Supported HMAC operations
 */
typedef enum hmac_ops { HMAC_OP_HMAC = 0, HMAC_OP_SHA256 = 1 } hmac_ops_t;

/**
 * HMAC Configuration options.
 */
typedef struct hmac_cfg {
  /** Operational mode @see hmac_ops. */
  hmac_ops_t mode;
  /** Set to 1 to swap input bytes. */
  uint32 input_endian_swap;
  /** Set to 1 to swap output bytes. */
  uint32 digest_endian_swap;
  /** Input key used in HMAC mode. */
  uint32 keys[8];
} hmac_cfg_t;

/**
 * Intialize HMAC to desired mode.
 *
 * @param hmac_cfg HMAC configuration settings.
 */
void hmac_init(hmac_cfg_t hmac_cfg);

/**
 * Write |size_in_bytes| bytes of |data| to HMAC input buffer
 *
 * @param data pointer to input buffer.
 * @param size_in_bytes number of bytes to write.
 */
void hmac_update(const void *data, usize size_in_bytes);

/**
 * Poll for hmac done and read out digest.
 *
 * @param digest pointer to output digest buffer.
 */
void hmac_done(uint32 *digest);

#endif  // _F_LIB_HMAC_H__
