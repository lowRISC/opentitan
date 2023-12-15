// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_MODINV_SCA_H_
#define OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_MODINV_SCA_H_

#include "sw/device/lib/crypto/drivers/otbn.h"

/**
 * The result of an OTBN SCA operation.
 */
typedef enum ecc256_modinv_sca_error {
  /**
   * Indicates that the operation succeeded.
   */
  ecc256ModinvOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  ecc256ModinvAborted = 1,
} ecc256_modinv_sca_error_t;

/**
 * App configuration for p256_mod_inv_sca
 */
OTBN_DECLARE_APP_SYMBOLS(p256_mod_inv_sca);

OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, k0);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, k1);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, kalpha_inv);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, alpha);

extern const otbn_app_t kOtbnAppP256ModInv;

static const otbn_addr_t kOtbnVarModInvK0;
static const otbn_addr_t kOtbnVarModInvK1;
static const otbn_addr_t kOtbnVarModInvKAplhaInv;
static const otbn_addr_t kOtbnVarModInvAlpha;

/**
 * Computes the modular inverse of a certain input.
 *
 * The input must be `kEcc256ModInvInputShareNumWords` words long.
 *
 * @param[in] input  Input for modular inverse computation.
 */
void ecc256_modinv(const uint8_t *k0_k1, size_t k0_k1_len);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CRYPTO_CRYPTOTEST_FIRMWARE_ECC256_MODINV_SCA_H_
