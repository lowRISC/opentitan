// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An owner_key can be either a ECDSA P256 or SPX+ key.  The type of the key
 * material will be determined by a separate field on the owner block
 */
typedef struct owner_key {
  uint32_t key[16];
} owner_key_t;

/**
 * An owner_signature is an ECDSA P256 signature.
 */
typedef struct owner_signature {
  uint32_t signature[16];
} owner_signature_t;

/**
 * The owner digest is a SHA256 digest.
 *
 * TODO(cfrantz): Unify this type with hmac_digest_t.
 */
typedef struct owner_digest {
  uint32_t digest[8];
} owner_digest_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_DATATYPES_H_
