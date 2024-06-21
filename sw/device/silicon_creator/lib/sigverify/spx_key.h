// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of an SPX public key in bits.
   */
  kSigverifySpxKeyNumBits = kSpxPkBytes * 8,
  /**
   * Size of an SPX public key in bytes.
   */
  kSigverifySpxKeyNumBytes = kSigverifySpxKeyNumBits / 8,
  /**
   * Size of an SPX public key in words.
   */
  kSigverifySpxKeyNumWords = kSigverifySpxKeyNumBytes / sizeof(uint32_t),
  /**
   * Size of an SPX root node in bits.
   */
  kSigverifySpxRootNumBits = kSpxN * 8,
  /**
   * Size of an SPX root node in bytes.
   */
  kSigverifySpxRootNumBytes = kSigverifySpxRootNumBits / 8,
  /**
   * Size of an SPX root node in words.
   */
  kSigverifySpxRootNumWords = kSigverifySpxRootNumBytes / sizeof(uint32_t),
  /**
   * Size of an SPX signature in bits.
   */
  kSigverifySpxSigNumBits = kSpxBytes * 8,
  /**
   * Size of an SPX signature in bytes.
   */
  kSigverifySpxSigNumBytes = kSigverifySpxSigNumBits / 8,
  /**
   * Size of an SPX signature in words.
   */
  kSigverifySpxSigNumWords = kSigverifySpxSigNumBytes / sizeof(uint32_t),
};

/**
 * SPX configuration ID.
 *
 * Used to identify the SPX parameter confuration used to sign/verify a message.
 *
 * Encoding generated with:
 * ./util/design/sparse-fsm-encode.py -d 6 -m 2 -n 32 -s 359186736 --language=c
 */
typedef enum sigverify_spx_config_id {
  /** SPHINCS+-SHA2-128s without pre-hashing. */
  kSigverifySpxConfigIdSha2128s = 0x0142410e,
  /**
   * SPHINCS+-SHA2-128s-q20 without pre-hashing.
   *
   * As specified in https://eprint.iacr.org/2022/1725.pdf.
   *
   * n  | h  | d | b  | k | w  | bitsec | sigsize
   * 16 | 18 | 1 | 24 | 6 | 16 |   128  | 3264
   */
  kSigverifySpxConfigIdSha2128sQ20 = 0x9b28d8da,
  /** SPHINCS+-SHA2-128s with SHA256 pre-hashing. */
  kSigverifySpxConfigIdSha2128sPrehash = 0x4694e9cb,
  /** SPHINCS+-SHA2-128s-q20 with SHA256 pre-hashing. */
  kSigverifySpxConfigIdSha2128sQ20Prehash = 0xa3ed7f9a,
} sigverify_spx_config_id_t;

/**
 * An SPX signature.
 */
typedef struct sigverify_spx_signature {
  /**
   * A `kSigverifySpxSigNumWords` base 2^32 digit integer, little-endian.
   */
  uint32_t data[kSigverifySpxSigNumWords];
} sigverify_spx_signature_t;

/**
 * An SPX public key.
 */
typedef struct sigverify_spx_key {
  /**
   * A `kSigverifySpxKeyNumWords` base 2^32 digit integer, little-endian.
   */
  uint32_t data[kSigverifySpxKeyNumWords];
} sigverify_spx_key_t;

/**
 * An SPX root node.
 */
typedef struct sigverify_spx_root {
  /**
   * A `kSigverifySpxRootNumWords` base 2^32 digit integer, little-endian.
   */
  uint32_t data[kSigverifySpxRootNumWords];
} sigverify_spx_root_t;

/**
 * Gets the ID of an SPX public key.
 *
 * ID of a key is its least significant word.
 * Callers must make sure that `key` is valid before calling this function.
 *
 * @param key An SPX public key.
 * @return ID of the key.
 */
OT_WARN_UNUSED_RESULT
inline uint32_t sigverify_spx_key_id_get(const sigverify_spx_key_t *key) {
  return key->data[0];
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_KEY_H_
