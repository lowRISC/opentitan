// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_CRYPTOLIB_BUILD_INFO_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_CRYPTOLIB_BUILD_INFO_H_

#include <stdint.h>

#include "sw/device/lib/crypto/include/datatypes.h"

/**
 * A truncated commit hash from the sw/device/lib/crypto directory from
 * the open-source OpenTitan repo that can be used to reproduce the
 * cryptolib binary.
 */
typedef struct cryptolib_build_info_scm_revision {
  /**
   * Least significant word of the truncated commit hash.
   */
  uint32_t scm_revision_low;
  /**
   * Most significant word of the truncated commit hash.
   */
  uint32_t scm_revision_high;
} cryptolib_build_info_scm_revision_t;

typedef struct cryptolib_build_info {
  /**
   * Truncated commit hash.
   */
  cryptolib_build_info_scm_revision_t scm_revision;
  /**
   * Cryptolib version.
   */
  uint32_t version;
  /**
   * Cryptolib released.
   */
  bool released;
} cryptolib_build_info_t;

enum {
  /**
   * Cryptolib version.
   * Currently the CL is in development, so this version is not
   * frozen.
   */
  kCryptoLibVersion = kOtcryptoLibVersion1,
  /**
   * Indicates whether the cryptolib is released or not.
   */
  kCryptoLibReleased = false,
};

/**
 * The build information.
 */
extern const cryptolib_build_info_t kCryptoLibBuildInfo;

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_CRYPTOLIB_BUILD_INFO_H_
