// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/params/params-sphincs-shake-128s.h
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/shake_offsets.h
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_PARAMS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_PARAMS_H_

/**
 * This file represents the SPHINCS+ parameter set shake-128s, meaning:
 * - The hash function is SHAKE-256
 * - >= 128 bits of security for up to 2^64 signatures
 * - The parameter set is optimized to be small "s" rather than fast "f"
 *   - The "fast" variant is faster for signing but actually slower for
 *     verification, so "s" is a better fit given we don't care about signing
 *     speed.
 *
 * For more details on parameterization, see the SPHINCS+ paper:
 * https://sphincs.org/data/sphincs+-paper.pdf
 */

enum {
  /**
   * Hash output length in bytes.
   */
  kSpxN = 16,
  /**
   * Height of the hypertree.
   */
  kSpxFullHeight = 63,
  /**
   * Number of subtree layers.
   */
  kSpxD = 7,
  /**
   * FORS tree dimension (height).
   */
  kSpxForsHeight = 12,
  /**
   * FORS tree dimension (number of trees).
   */
  kSpxForsTrees = 14,
  /**
   * Winternitz parameter.
   */
  kSpxWotsW = 16,
  /**
   * Number of bytes in a hypertree address (for clarity).
   */
  kSpxAddrBytes = 32,
  /**
   * Bit-length of the Winternitz parameter.
   */
  kSpxWotsLogW = 4,
  /**
   * Parameter `len1` for WOTS signatures.
   *
   * See section 3.1 of the SPHINCS+ NIST submission:
   *   https://sphincs.org/data/sphincs+-r3.1-specification.pdf
   */
  kSpxWotsLen1 = (8 * kSpxN) / kSpxWotsLogW,
  /**
   * Parameter `len2` for WOTS signatures.
   *
   * This value is precomputed and equal to:
   *   floor(log(len1 * (w - 1)) / log(w)) + 1
   *
   * During the WOTS computation, the maximum checksum value is `len1 * (w -
   * 1)`. The log() functions here essentially apply the change-of-base rule;
   * what we are actually computing is floor(log_w(len1 * (w - 1))) + 1, which
   * expresses the number of base-w integers required to encode the checksum.
   *
   * Some precomputed values based on w and n:
   *   +------+----------------+----------+
   *   |  w   |        n       |   len2   |
   *   +------+----------------+----------+
   *   | 256  |   0 < n <= 1   |    1     |
   *   | 256  |   1 < n <= 256 |    2     |
   *   |  16  |   0 < n <= 8   |    2     |
   *   |  16  |   8 < n <= 136 |    3     |
   *   |  16  | 136 < n <= 256 |    4     |
   *   +------+----------------+----------+
   *
   * See section 3.1 of the SPHINCS+ NIST submission:
   *   https://sphincs.org/data/sphincs+-r3.1-specification.pdf
   */
  kSpxWotsLen2 = 3,
  /**
   * Number of chains to compute for a WOTS signature.
   */
  kSpxWotsLen = kSpxWotsLen1 + kSpxWotsLen2,
  /**
   * WOTS signature length in bytes.
   *
   * The signature is composed of `kSpxWotsLen` blocks of `kSpxN` bytes each.
   */
  kSpxWotsBytes = kSpxWotsLen * kSpxN,
  /**
   * WOTS public key length in bytes.
   */
  kSpxWotsPkBytes = kSpxWotsBytes,
  /**
   * Subtree size.
   */
  kSpxTreeHeight = kSpxFullHeight / kSpxD,
  /**
   * FORS message length.
   */
  kSpxForsMsgBytes = ((kSpxForsHeight * kSpxForsTrees) + 7) / 8,
  /**
   * FORS signature length.
   */
  kSpxForsBytes = (kSpxForsHeight + 1) * kSpxForsTrees * kSpxN,
  /**
   * FORS public key length.
   */
  kSpxForsPkBytes = kSpxN,
  /**
   * SPHINCS+ signature.
   */
  kSpxBytes =
      kSpxN + kSpxForsBytes + kSpxD * kSpxWotsBytes + kSpxFullHeight * kSpxN,
  /**
   * SPHINCS+ public key length.
   */
  kSpxPkBytes = 2 * kSpxN,
  /**
   * SPHINCS+ secret key length.
   */
  kSpxSkBytes = 2 * kSpxN + kSpxPkBytes,
  /**
   * Hash output length (n) in words.
   */
  kSpxNWords = kSpxN / sizeof(uint32_t),
  /**
   * FORS signature size in words.
   */
  kSpxForsWords = kSpxForsBytes / sizeof(uint32_t),
  /**
   * WOTS signature size in words.
   */
  kSpxWotsWords = kSpxWotsBytes / sizeof(uint32_t),
  /**
   * WOTS public key size in words.
   */
  kSpxWotsPkWords = kSpxWotsPkBytes / sizeof(uint32_t),
  /**
   * SPHINCS+ public key length in words.
   */
  kSpxPkWords = kSpxPkBytes / sizeof(uint32_t),
};

/**
 * These constants are byte offsets within the hypertree address structure.
 *
 * It is customized for the hypertree address format that is used when SHAKE is
 * the underlying SPHINCS+ hash function. These values should not change if
 * parameters other than the hash function are altered.
 */
enum {
  /**
   * Byte used to specify the Merkle tree layer.
   */
  kSpxOffsetLayer = 3,
  /**
   * Starting byte of the tree field (8 bytes).
   */
  kSpxOffsetTree = 8,
  /**
   * Byte used to specify the hash type (reason).
   */
  kSpxOffsetType = 19,
  /**
   * High byte of the key pair.
   */
  kSpxOffsetKpAddr2 = 22,
  /**
   * Low byte of the key pair.
   */
  kSpxOffsetKpAddr1 = 23,
  /**
   * Byte for the chain address (i.e. which Winternitz chain).
   */
  kSpxOffsetChainAddr = 27,
  /**
   * Byte for the hash address (i.e. where in the Winternitz chain).
   */
  kSpxOffsetHashAddr = 31,
  /**
   * Byte for the height of this node in the FORS or Merkle tree.
   */
  kSpxOffsetTreeHeight = 27,
  /**
   * Starting byte for the tree index field (4 bytes) in the FORS or Merkle
   * tree.
   */
  kSpxOffsetTreeIndex = 28,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_PARAMS_H_
