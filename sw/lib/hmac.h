// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _F_LIB_HMAC_H__
#define _F_LIB_HMAC_H__

#include <stddef.h>
#include <stdint.h>

/* hmac operations */
typedef enum hmac_ops { Hmac = 0, Sha256 = 1 } hmac_ops_t;

typedef struct hmac_cfg {
  hmac_ops_t mode;
  // input swapping only (from reg)
  uint32_t input_endian_swap;
  // output swapping only (to digest)
  uint32_t digest_endian_swap;
  // length in bits
  uint32_t length_lower;
  // lenght in bits
  uint32_t length_upper;
  uint32_t keys[8];
} hmac_cfg_t;

/* Intialize hmac to desired mode. */
void hmac_init(hmac_cfg_t hmac_cfg);

/* Returns 1 if hmac fifo is full, 0 otherwise. */
int hmac_fifo_full(void);

/* Write |data| to hmac with |size| in Bytes */
void hmac_write(const void *data, size_t size);

/* Poll for hmac done and read out digest. */
int hmac_done(uint32_t *digest);

#endif  // _F_LIB_HMAC_H__
