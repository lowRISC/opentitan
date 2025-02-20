// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <bitset>
#include <ostream>
#include <stdint.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

// Reach into math_builtins.c and grab the internal testing symbols.
extern "C" {
int64_t _ot_builtin_lshift_i64(int64_t val, int32_t shift);
int64_t _ot_builtin_rshift_i64(int64_t val, int32_t shift);
int64_t _ot_builtin_ashift_i64(int64_t val, int32_t shift);

int32_t _ot_builtin_bswap_i32(int32_t val);
int _ot_builtin_popcount_i32(int32_t val);
int _ot_builtin_parity_i32(int32_t val);

int _ot_builtin_clz_i32(int32_t val);
int _ot_builtin_ctz_i32(int32_t val);
int _ot_builtin_find_first_i32(int32_t val);
}

namespace math_unittest {
namespace {

class ShiftTest : public testing::TestWithParam<std::tuple<uint64_t, int>> {};

TEST_P(ShiftTest, LShift) {
  auto val = std::get<0>(GetParam());
  auto sh = std::get<1>(GetParam());
  EXPECT_EQ(_ot_builtin_lshift_i64(val, sh), val << sh);
}

TEST_P(ShiftTest, RShift) {
  auto val = std::get<0>(GetParam());
  auto sh = std::get<1>(GetParam());
  EXPECT_EQ(_ot_builtin_rshift_i64(val, sh), val >> sh);
}

TEST_P(ShiftTest, AShift) {
  int64_t val = std::get<0>(GetParam());
  auto sh = std::get<1>(GetParam());
  EXPECT_EQ(_ot_builtin_ashift_i64(val, sh), val >> sh);
}

// clang-format off
constexpr uint64_t kShiftVectors[] = {
  0x72e31374b288d54b, 0xe3803f2635f6ee6f, 0xba25acc04b1c109f, 0xc47399918b992246,
  0xfcd337f4a9657652, 0xad1d516938ba9e58, 0xcaf2ea72ecab24ce, 0xe575c95799b3fd25,
  0x7179d63f5318a042, 0x66cb3b7bafa9ab91, 0x01e3a61671afb124, 0x883dec25388a7d17,
  0x2409a453b22f2afb, 0xa3a22aaf52b455a6, 0xe6aafa4b21df3fde, 0x1ab66cae8bf7f70a,
  0xa2c5ce0f7a8c39ae, 0xb4dfee68dc55a333, 0x424a9080c3eb7f28, 0x33e20b7ad01ed2d3,
  0x012986549ba5c18e, 0x71470e3eab601397, 0x7c641906111c4a97, 0x4947714cc88fa328,
  0x95ef5317cba3383a, 0x8cc65207c9a01c75, 0xbacd69c7b9f07da5, 0x7ea168d4980e39b1,
  0xfd434457e60eea3b, 0xfb06cbaefee8dac0, 0x59c6cbe506da5009, 0x17384e6055a26fda,
  0x5f7a2b0fb58b3d5b, 0x04581fca7eca14c5, 0xb0e85631e03a2f5f, 0x072ef34c9ffe2af0,
  0xb7a8416d262ab414, 0xaaeda113b5c0f99b, 0x5ec1edc1bb424e4c, 0xd7a6efda2c1adfd9,
  0x58c00ce60adee54e, 0x2738634afbe4fa68, 0xfbd84af315127e70, 0xd7b1c602bbc5f287,
  0xa87ed34fade4ca9e, 0x274c0d4536a73a4f, 0x6bd60d1fbd5dd8bf, 0x3e3480053ffa2b32,
  0xe4509fb8d04198c7, 0x1ca94e3528b69802, 0xc1db8afa638209dd, 0xf3b127563b4e67e6,
  0x55945fc85fce5a15, 0x2f46dfdd59dc99bb, 0xd305bd01c6fc90cb, 0xb6f3e737ae6852e2,
  0x23a1a2588da1b8bc, 0xa9e4f54d6aa91ab0, 0x754b06a594c37253, 0x530d325ad21250ad,
  0x9ba1df480099e563, 0xaeddb8f02430fa05, 0x95420781c1434885, 0x7ef252bb0353cc94,
  0x360b0516971db663, 0xd984feb6fb7f383d, 0xe76cb6124460dce4, 0x00b449c6afad532c,
  0x9549d9a4db6698bd, 0x472176983d94969d, 0x44203ca1c11f6698, 0x316b015904b9a585,
  0xef529bbe99f8789d, 0x6797c2899a4a6338, 0x5856d8199b694d0d, 0x40d8a06d9ea5d550,
  0x063371e154698005, 0xd0b4a74656dfacc3, 0x904d67ecddc9bdc1, 0xf3da1b4f14a8ee38,
  0xa7f2008e10ff5104, 0xc971d6076bb18705, 0x542052cbcf18e642, 0x8bc461ce47296918,
  0x050cd8d5a1d205f5, 0x96b852ad44647978, 0xf06eb96bb06c5014, 0x7f34e0824755f34d,
  0xef2bad1655aa4af3, 0xfa2a29654ec5cde7, 0x25c5b8b6be8210f9, 0xdb2abc045c3debf2,
  0xc87cd628ca86ee17, 0x754dcf0f9ef1f43f, 0x5b41d1713ec1d622, 0xf04e0ccadb55f484,
  0x91cc30dba5cb088a, 0x8fadd12094d86765, 0x4b32b8bf703b2bcb, 0x2b388b7267361d11,
  0x796c96e61c5cee34, 0xa422df223c6f4386, 0x2c73a57443bd8e55, 0x5055ba2568f0840e,
  0x2c12963cc6252411, 0x2866daa721519adf, 0x9cf9fc214a9bf499, 0xd2a1b710d03a83c8,
  0x4aaefeec333d2bc6, 0x74f426e6c662351d, 0xca9137650e7ff7ff, 0x81a59590069af3df,
  0x90413762d48e5fe4, 0x9acdf15570b4d51a, 0x7a18f080c38fbe68, 0x4819af998c5480b5,
  0x0b1ab546043e8c39, 0x5c41cd7dcd416951, 0x123138f887109c2d, 0xa75ed843bf10be7e,
  0xfd1361e852c595f0, 0xa9346bdc942d64db, 0xb090a120f73defb7, 0xff73e1a0c52dbc5e,
  0x3f32be41f8ba8b90, 0x72f3825c514d8bb8, 0xe4f28307980edcd7, 0x373036b9647f0a8b,
};
// clang-format on

INSTANTIATE_TEST_SUITE_P(ShiftTest, ShiftTest,
                         testing::Combine(testing::ValuesIn(kShiftVectors),
                                          testing::Range(0, 63)));

}  // namespace
}  // namespace math_unittest
