// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ATTESTATION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ATTESTATION_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of the additional seed for attestation key generation in bits.
   */
  kAttestationSeedBits = 320,
  /**
   * Size of the additional seed for attestation key generation in bytes.
   */
  kAttestationSeedBytes = kAttestationSeedBits / 8,
  /**
   * Size of the additional seed for attestation key generation in 32b words.
   */
  kAttestationSeedWords = kAttestationSeedBytes / sizeof(uint32_t),
};

/**
 * Attestation key generation scheme version.
 */
enum {
  kAttestationKeyGenVersion0 = 0,
};

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ATTESTATION_H_
