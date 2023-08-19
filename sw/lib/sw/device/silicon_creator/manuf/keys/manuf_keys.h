// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_KEYS_MANUF_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_KEYS_MANUF_KEYS_H_

#include "sw/device/lib/crypto/include/ecc.h"

/**
 * ECDH Public key from HSM for generating the ephemeral RMA unlock token
 * symmetric encryption key.
 */
extern const ecc_public_key_t kRmaUnlockTokenExportKeyPkHsm;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_KEYS_MANUF_KEYS_H_
