// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * A nonce value used for challenge/response in boot services message.
 */
typedef struct nonce {
  uint32_t value[2];
} nonce_t;

/**
 * Generate a new nonce random nonce value.
 *
 * @param nonce Pointer to a nonce.
 */
void nonce_new(nonce_t *nonce);

/**
 * Check nonces for equality.
 *
 * @param a Nonce to compare.
 * @param b Nonce to compare.
 * @return bool true if equal, false otherwise.
 */
inline bool nonce_equal(const nonce_t *a, const nonce_t *b) {
  return a->value[0] == b->value[0] && a->value[1] == b->value[1];
}

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_
