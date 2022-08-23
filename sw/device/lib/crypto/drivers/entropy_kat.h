// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_KAT_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_KAT_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Run CTR DRBG Known-Answer-Tests (KATs) on SW CSRNG instance.
 *
 * Test vector sourced from NIST's CAVP website:
 * https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators
 *
 * The number format in this docstring follows the CAVP format to simplify
 * auditing of the implementation.
 *
 * Test vector: CTR_DRBG AES-256 no DF.
 *
 * - EntropyInput =
 * df5d73faa468649edda33b5cca79b0b05600419ccb7a879ddfec9db32ee494e5531b51de16a30f769262474c73bec010
 * - Nonce = EMPTY
 * - PersonalizationString = EMPTY
 *
 * Command: Instantiate
 * - Key = 8c52f901632d522774c08fad0eb2c33b98a701a1861aecf3d8a25860941709fd
 * - V   = 217b52142105250243c0b2c206b8f59e
 *
 * Command: Generate (first call):
 * - Key = 72f4af5c93258eb3eeec8c0cacea6c1d1978a4fad44312725f1ac43b167f2d52
 * - V   = e86f6d07dfb551cebad80e6bf6830ac4
 *
 * Command: Generate (second call):
 * - Key = 1a1c6e5f1cccc6974436e5fd3f015bc8e9dc0f90053b73e3c19d4dfd66d1b85a
 * - V   = 53c78ac61a0bac9d7d2e92b1e73e3392
 * - ReturnedBits =
 * d1c07cd95af8a7f11012c84ce48bb8cb87189e99d40fccb1771c619bdf82ab2280b1dc2f2581f39164f7ac0c510494b3a43c41b7db17514c87b107ae793e01c5
 *
 * @return Operation status in `status_t` format.
 */
status_t entropy_csrng_kat(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_KAT_H_
