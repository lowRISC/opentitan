// Copyright lowRISC contributors (OpenTitan project).
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
 * Test vector sourced from NIST's CAVP SP 800-90A DRBG test vectors:
 * - Page:
 * https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/random-number-generators
 * - Archive:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip
 * - OpenTitan mirror:
 * https://storage.googleapis.com/ot-crypto-test-vectors/nist/drbgtestvectors.zip
 *   (Bazel repo `@nist_cavp_drbg_sp_800_90a_root` in
 * `third_party/nist_cavp_testvectors/extensions.bzl`)
 * - Path inside archive: `drbgvectors_pr_true.zip` -> `CTR_DRBG.txt`
 * - Section: `[AES-256 no df]`, `[PredictionResistance = True]`, `COUNT = 0`
 *
 * Note: In NIST SP 800-90A PredictionResistance mode, each `GENERATE` call
 * performs a `Reseed(EntropyInputPR)` before generating bits. `CTR_DRBG.txt`
 * prints `(Key, V)` after `INSTANTIATE` and after each `GENERATE` call; the
 * `(Key, V)` values under `Command: Reseed` below are the intermediate states
 * right after `CTR_DRBG_Reseed(EntropyInputPR)`.
 *
 * The number format in this docstring follows the CAVP format to simplify
 * auditing of the implementation.
 *
 * - EntropyInput =
 * faf346c9c8afbc5ab6e33ce492247fac6db9a7ba4297557f587a42563ddf56c90e41c6afb56233815b74e091bac7d8e5
 * - Nonce = EMPTY
 * - PersonalizationString = EMPTY
 *
 * Command: Instantiate
 * - Key = a9fccc320fea8ae31f80881556ef0c27a31ee7870ff73e115f348785872ccbd1
 * - V   = 7c21c56582c419f58ad6151fcfc1ed6b
 *
 * Command: Reseed (first call):
 * - EntropyInputPR =
 * dfc111252d7146922713720ae1e348a07ae403b5238fefb4e8592f6f6cc4a61c94828db84c6faecd1502261008011f2c
 * - AdditionalInput = EMPTY
 * - Key = 3e5aac1e345d4ab78d164cd0e86aa79d5632585acc781d261d37a9adc2d77b37
 * - V   = 7759eaf5061a7547e0c7a00272488149
 *
 * Command: Generate (first call):
 * - AdditionalInput = EMPTY
 * - Key = 59ab2aa229c17b2ccf5b633ad905aa4396d717cd7109c4396176b445e23b54b0
 * - V   = 9ac50e38805dab58baf6429436e00b39
 *
 * Command: Reseed (second call):
 * - EntropyInputPR =
 * 4528bac5b99c772347d44f4ece79bc811ca8ebea9483fa5f5040c02f77069dad1aec7adaa8a9a6a9ddabab045d328a90
 * - AdditionalInput = EMPTY
 * - Key = b71fc243f87af33465a10e16e9da54ffd334b7d15148c995e1fa401ce7f57744
 * - V   = cc911b3b04acd7ac99e18aa22389b4ba
 *
 * Command: Generate (second call):
 * - AdditionalInput = EMPTY
 * - Key = 48f4632bbc79c4bde48a8588a5395afcdccc84f2a3b25b8be2715cd8f9dd8a6b
 * - V   = 24f485205e3baf899b8c226c2ffc73ce
 * - ReturnedBits =
 * bc013dc891db12c34ad11944805bf13dfd67ff2c23176d83f5b396b69e400042252e11816c3095421137181a5d0ee37c83a339c58d080946ca90aa437d50d9cf
 *
 * @return Operation status in `status_t` format.
 */
status_t entropy_csrng_kat(void);

/**
 * Run Known-Answer-Test (KAT) on the entropy_src SHA-3 conditioning.
 *
 * Configures entropy_src into firmware override mode, pushes 12 words of
 * known message input into the WR_DATA FIFO, reads the resulting digest,
 * and verifies it matches the expected SHA-3 conditioning digest.
 *
 * @return Operation status in `status_t` format.
 */
status_t entropy_src_sha3_conditioning_kat(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_KAT_H_
