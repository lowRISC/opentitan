// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_ECC256_KEYGEN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_ECC256_KEYGEN_SCA_H_

#include "sw/device/lib/crypto/drivers/otbn.h"

/**
 * App configuration for p256_key_from_seed_sca
 */
OTBN_DECLARE_APP_SYMBOLS(p256_key_from_seed_sca);

OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, mode);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, seed0);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, seed1);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, d0);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, d1);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, x);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, y);

extern const otbn_app_t kOtbnAppP256KeyFromSeed;

static const otbn_addr_t kOtbnVarMode;
static const otbn_addr_t kOtbnVarSeed0;
static const otbn_addr_t kOtbnVarSeed1;
static const otbn_addr_t kOtbnVarD0;
static const otbn_addr_t kOtbnVarD1;

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_SCA_ECC256_KEYGEN_SCA_H_
