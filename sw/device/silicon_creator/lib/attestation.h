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

typedef enum {
  /**
   * The UDS attestation key seed.
   */
  kUdsAttestationKeySeed = 0,
  /**
   * The CDI_0 attestation key seed.
   */
  kCdi0AttestationKeySeed = 1,
  /**
   * The CDI_1 attestation key seed.
   */
  kCdi1AttestationKeySeed = 2,
  /**
   * The TPM EK attestation key seed.
   */
  kTpmEkAttestationKeySeed = 3,
  /**
   * The TPM CEK attestation key seed.
   */
  kTpmCekAttestationKeySeed = 4,
  /**
   * The TPM CIK attestation key seed.
   */
  kTpmCikAttestationKeySeed = 5,
} attestation_key_seed_t;

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
