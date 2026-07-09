// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CRYPTOLIB_BUILD_INFO_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CRYPTOLIB_BUILD_INFO_H_

#include <stdbool.h>

#include "datatypes.h"

/**
 * @file
 * @brief Cryptolib build information.
 *
 * Returns the version of the cryptolib as well as the git hash.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Read the cryptolib build information.
 *
 * Returns the current version of the cryptolib as well as the
 * latest git commit hash of the `sw/device/lib/crypto` directory.
 *
 * To get the actual git commit hash and mark the build as released,
 * the build must be run with the Bazel `--stamp` option. Otherwise,
 * a default placeholder hash is used and the library is marked as unreleased.
 *
 * @param[out] version The current version of the cryptolib.
 * @param[out] released Whether this is a release build (enabled via `--stamp`).
 * @param[out] build_hash_low The low portion of the git commit hash of
 * `sw/device/lib/crypto`.
 * @param[out] build_hash_high The high portion of the git commit hash of
 * `sw/device/lib/crypto`.
 * @return Status of the operation.
 */
otcrypto_status_t otcrypto_build_info(uint32_t *version, bool *released,
                                      uint32_t *build_hash_low,
                                      uint32_t *build_hash_high);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_CRYPTOLIB_BUILD_INFO_H_
