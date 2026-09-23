// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstddef>
#include <cstdint>
#include <cstring>

#include "gtest/gtest.h"

extern "C" {
#include "third_party/embedpqc/mldsa_tiny_common.h"
#include "third_party/embedpqc/ports/shake.h"

static size_t g_squeeze_call_count = 0;

void __wrap_SHAKE256_init(shake256_ctxt_t *ctxt) {
  (void)ctxt;
  g_squeeze_call_count = 0;
}

void __wrap_SHAKE256_absorb(shake256_ctxt_t *ctxt, const uint8_t *in,
                            size_t in_len) {
  (void)ctxt;
  (void)in;
  (void)in_len;
}

void __wrap_SHAKE256_squeeze(shake256_ctxt_t *ctxt, uint8_t *out,
                             size_t out_len) {
  (void)ctxt;
  ++g_squeeze_call_count;
  if (g_squeeze_call_count == 1) {
    // First 136-byte SHAKE256 block:
    // - Bytes [0..7] hold the 64 sign bits (alternating 0 and 1 bits).
    // - Bytes [8..135] are 0xFF (255), which are all rejected when i = 217
    //   (since 255 > 217), forcing `offset` to reach 136 and squeeze a
    //   second SHAKE256 block.
    memset(out, 0xAA, 8);
    memset(out + 8, 0xFF, out_len - 8);
  } else {
    // Second 136-byte SHAKE256 block:
    // Provide valid candidate index bytes (0 <= i) so all tau=39 iterations
    // succeed from the refilled block.
    for (size_t idx = 0; idx < out_len; ++idx) {
      out[idx] = static_cast<uint8_t>(idx & 0x7F);
    }
  }
}

void __wrap_SHAKE256_free(shake256_ctxt_t *ctxt) { (void)ctxt; }
}  // extern "C"

namespace {

TEST(MldsaTinyCommonTest, SampleInBallRefillsBlockOnRejectionOverflow) {
  constexpr size_t kMldsa44Tau = 39;
  const uint8_t kSeed[32] = {0};
  scalar_t c;

  scalar_sample_in_ball_vartime(kMldsa44Tau, &c, kSeed, sizeof(kSeed));

  // Verify that the rejection loop exhausted the initial 136-byte block and
  // squeezed a second 136-byte block at `offset == 136`.
  EXPECT_EQ(g_squeeze_call_count, 2u);

  // Verify that the output polynomial has Hamming weight `tau = 39` and all
  // non-zero coefficients are in {1, K_PRIME - 1}.
  size_t non_zero_count = 0;
  for (size_t i = 0; i < K_DEGREE; ++i) {
    if (c.c[i] != 0) {
      ++non_zero_count;
      EXPECT_TRUE(c.c[i] == 1 || c.c[i] == K_PRIME - 1);
    }
  }
  EXPECT_EQ(non_zero_count, kMldsa44Tau);
}

}  // namespace
