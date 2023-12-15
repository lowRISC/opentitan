// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_KEYGEN_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_KEYGEN_SCA_H_

#include "sw/device/lib/crypto/drivers/otbn.h"

/**
 * The result of an OTBN SCA operation.
 */
typedef enum ecc256_keygen_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  ecc256KeygenOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  ecc256KeygenAborted = 1,
} ecc256_keygen_sca_error_t;

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
static const otbn_addr_t kOtbnVarX;
static const otbn_addr_t kOtbnVarY;

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_KEYGEN_SCA_H_
