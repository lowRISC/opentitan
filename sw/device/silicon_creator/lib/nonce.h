// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_

#include <stdint.h>

/**
 * A nonce value used for challenge/response in boot services message.
 */
typedef struct nonce {
  uint32_t value[2];
} nonce_t;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NONCE_H_
