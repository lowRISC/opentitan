// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"

#include <array>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace ghash_unittest {
namespace {
using ::testing::ElementsAreArray;

TEST(Ghash, McGrawViegaTestCase1) {
  // GHASH computation from test case 1 of:
  // https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
  //
  // H: 66e94bd4ef8a2c3b884cfa59ca342b2e
  // A: empty
  // C: empty
  // GHASH(H,A,C): 00000000000000000000000000000000
  std::array<uint32_t, 4> H = {
      0xd44be966,
      0x3b2c8aef,
      0x59fa4c88,
      0x2e2b34ca,
  };
  std::array<uint32_t, 4> exp_result = {0, 0, 0, 0};

  // Compute GHASH(H, A, C).
  ghash_context_t ctx;
  ghash_init_subkey(H.data(), &ctx);
  ghash_init(&ctx);
  uint32_t result[kGhashBlockNumWords];
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(exp_result));
}

TEST(Ghash, Mul1) {
  // Multiply the hash subkey by 1.
  // H: 66e94bd4ef8a2c3b884cfa59ca342b2e
  // GHASH(H,1) = H
  std::array<uint32_t, 4> H = {
      0xd44be966,
      0x3b2c8aef,
      0x59fa4c88,
      0x2e2b34ca,
  };
  // Big-endian form of 1.
  uint8_t one = 0x80;

  ghash_context_t ctx;
  ghash_init_subkey(H.data(), &ctx);
  ghash_init(&ctx);
  ghash_update(&ctx, 1, &one);
  uint32_t result[kGhashBlockNumWords];
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(H));
}

TEST(Ghash, McGrawViegaTestCase2) {
  // GHASH computation from test case 2 of:
  // https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
  //
  // H: 66e94bd4ef8a2c3b884cfa59ca342b2e
  // A: empty
  // C: 0388dace60b6a392f328c2b971b2fe78
  // GHASH(H,A,C): f38cbb1ad69223dcc3457ae5b6b0f885
  std::array<uint32_t, 4> H = {
      0xd44be966,
      0x3b2c8aef,
      0x59fa4c88,
      0x2e2b34ca,
  };
  std::array<uint32_t, 0> A = {};
  std::array<uint32_t, 4> C = {
      0xceda8803,
      0x92a3b660,
      0xb9c228f3,
      0x78feb271,
  };
  std::array<uint32_t, 4> exp_result = {
      0x1abb8cf3,
      0xdc2392d6,
      0xe57a45c3,
      0x85f8b0b6,
  };

  // Encode bitlengths of A and C as big-endian 64-bit integers.
  std::array<uint64_t, 2> bitlengths = {
      A.size() * sizeof(uint32_t) * 8,
      C.size() * sizeof(uint32_t) * 8,
  };
  bitlengths[0] = __builtin_bswap64(bitlengths[0]);
  bitlengths[1] = __builtin_bswap64(bitlengths[1]);

  // Compute GHASH(H, A, C).
  ghash_context_t ctx;
  ghash_init_subkey(H.data(), &ctx);
  ghash_init(&ctx);
  ghash_update(&ctx, A.size() * sizeof(uint32_t), (unsigned char *)A.data());
  ghash_update(&ctx, C.size() * sizeof(uint32_t), (unsigned char *)C.data());
  ghash_update(&ctx, bitlengths.size() * sizeof(uint64_t),
               (unsigned char *)bitlengths.data());
  uint32_t result[kGhashBlockNumWords];
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(exp_result));
}

TEST(Ghash, ContextReset) {
  // Run a test case twice to ensure that (a) the hash state is properly reset
  // by `init()`, so that the result is correct both times and (b) the hash
  // subkey is not cleared by `init()`.
  std::array<uint32_t, 4> H = {
      0xd44be966,
      0x3b2c8aef,
      0x59fa4c88,
      0x2e2b34ca,
  };
  std::array<uint32_t, 0> A = {};
  std::array<uint32_t, 4> C = {
      0xceda8803,
      0x92a3b660,
      0xb9c228f3,
      0x78feb271,
  };
  std::array<uint32_t, 4> exp_result = {
      0x1abb8cf3,
      0xdc2392d6,
      0xe57a45c3,
      0x85f8b0b6,
  };

  // Encode bitlengths of A and C as big-endian 64-bit integers.
  std::array<uint64_t, 2> bitlengths = {
      A.size() * sizeof(uint32_t) * 8,
      C.size() * sizeof(uint32_t) * 8,
  };
  bitlengths[0] = __builtin_bswap64(bitlengths[0]);
  bitlengths[1] = __builtin_bswap64(bitlengths[1]);

  // Initialize the hash subkey (should only need to do this once).
  ghash_context_t ctx;
  ghash_init_subkey(H.data(), &ctx);

  // Compute GHASH(H, A, C).
  ghash_init(&ctx);
  ghash_update(&ctx, A.size() * sizeof(uint32_t), (unsigned char *)A.data());
  ghash_update(&ctx, C.size() * sizeof(uint32_t), (unsigned char *)C.data());
  ghash_update(&ctx, bitlengths.size() * sizeof(uint64_t),
               (unsigned char *)bitlengths.data());
  uint32_t result[kGhashBlockNumWords];
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(exp_result));

  // Compute GHASH(H, A, C) a second time.
  ghash_init(&ctx);
  ghash_update(&ctx, A.size() * sizeof(uint32_t), (unsigned char *)A.data());
  ghash_update(&ctx, C.size() * sizeof(uint32_t), (unsigned char *)C.data());
  ghash_update(&ctx, bitlengths.size() * sizeof(uint64_t),
               (unsigned char *)bitlengths.data());
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(exp_result));
}

TEST(Ghash, McGrawViegaTestCase18) {
  // GHASH computation from test case 18 of:
  // https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
  //
  // H: acbef20579b4b8ebce889bac8732dad7
  // A: feedfacedeadbeeffeedfacedeadbeefabaddad2
  // C:
  // 5a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f
  // GHASH(H,A,C): d5ffcf6fc5ac4d69722187421a7f170b
  std::array<uint32_t, 4> H = {
      0x05f2beac,
      0xebb8b479,
      0xac9b88ce,
      0xd7da3287,
  };
  std::array<uint32_t, 5> A = {
      0xcefaedfe, 0xefbeadde, 0xcefaedfe, 0xefbeadde, 0xd2daadab,
  };
  std::array<uint32_t, 15> C = {
      0x2fef8d5a, 0xf1539e0c, 0x53785df7, 0x202a9e65, 0x2ab2b2ee,
      0x1964deaf, 0x4fab58a0, 0xf46b746f, 0xb7c3c00f, 0x4544f280,
      0xf1eba32d, 0xde2cd8c5, 0x978941a2, 0x2ef80e20, 0x3f7eae44,
  };
  std::array<uint32_t, 4> exp_result = {
      0x6fcfffd5,
      0x694dacc5,
      0x42872172,
      0x0b177f1a,
  };

  // Encode bitlengths of A and C as big-endian 64-bit integers.
  std::array<uint64_t, 2> bitlengths = {
      A.size() * sizeof(uint32_t) * 8,
      C.size() * sizeof(uint32_t) * 8,
  };
  bitlengths[0] = __builtin_bswap64(bitlengths[0]);
  bitlengths[1] = __builtin_bswap64(bitlengths[1]);

  // Compute GHASH(H, A, C).
  ghash_context_t ctx;
  ghash_init_subkey(H.data(), &ctx);
  ghash_init(&ctx);
  ghash_update(&ctx, A.size() * sizeof(uint32_t), (unsigned char *)A.data());
  ghash_update(&ctx, C.size() * sizeof(uint32_t), (unsigned char *)C.data());
  ghash_update(&ctx, bitlengths.size() * sizeof(uint64_t),
               (unsigned char *)bitlengths.data());
  uint32_t result[kGhashBlockNumWords];
  ghash_final(&ctx, result);

  EXPECT_THAT(result, testing::ElementsAreArray(exp_result));
}

}  // namespace
}  // namespace ghash_unittest
