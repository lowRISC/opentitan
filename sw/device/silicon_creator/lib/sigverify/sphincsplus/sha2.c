// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/7ec789ace6874d875f4bb84cb61b81155398167e/ref/sha2.c

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

void mgf1_sha256(const uint32_t *in, size_t in_len, size_t out_len,
                 uint32_t *out) {
  // Append SHA256(in || counter) to the output until the requested length is
  // reached.
  for (uint32_t ctr = 0; ctr * kHmacDigestNumWords < out_len; ctr++) {
    hmac_sha256_init_endian(/*big_endian=*/true);
    hmac_sha256_update_words(in, in_len);
    uint32_t ctr_be = __builtin_bswap32(ctr);
    hmac_sha256_update_words(&ctr_be, 1);
    // If the remaining output needed is less than the full digest size,
    // truncate.
    size_t digest_words =
        (out_len <= kHmacDigestNumWords) ? out_len : kHmacDigestNumWords;
    hmac_sha256_final_truncated(out, digest_words);
    out += digest_words;
  }
}
