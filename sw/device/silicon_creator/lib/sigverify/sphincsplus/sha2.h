// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/7ec789ace6874d875f4bb84cb61b81155398167e/ref/sha2.h

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_SHA2_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_SHA2_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

static_assert(kSpxSha512 == 0,
              "Parameter sets requiring SHA-512 are not supported.");

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Number of bytes in the SHA256 block size (512 bits).
   */
  kSpxSha2BlockNumBytes = 512 / 8,
  /**
   * Number of words in the SHA256 block size.
   */
  kSpxSha2BlockNumWords = kSpxSha2BlockNumBytes / sizeof(uint32_t),
  /**
   * Total number of bytes in the SHA256 address representation.
   */
  kSpxSha256AddrBytes = 22,
};

/**
 * Mask-generation function (MGF1) using SHA256.
 *
 * MGF1 is defined in IETF RFC 8017, section B.2.1. Its inputs are a seed and a
 * length, and it produces a mask value of that length from the seed using an
 * underlying hash function (SHA256 in this case).
 *
 * The input and output buffers are allowed to overlap in any configuration.
 *
 * @param in Input buffer.
 * @param in_len Input buffer length in 32-bit words.
 * @param out_len Requested output length in 32-bit words.
 * @param[out] out Output buffer.
 */
void mgf1_sha256(const uint32_t *in, size_t in_len, size_t out_len,
                 uint32_t *out);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_SHA2_H_
