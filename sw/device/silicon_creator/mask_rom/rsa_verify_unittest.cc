// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/rsa_verify.h"

#include <unordered_set>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace rsa_verify_unittest {
namespace {

TEST(Keys, UniqueIds) {
  std::unordered_set<uint32_t> ids;
  for (auto const &key : kSigVerifyRsaKeys) {
    ids.insert(sigverify_rsa_key_id_get(&key));
  }

  EXPECT_EQ(ids.size(), kSigVerifyNumRsaKeys);
}

/**
 * An RSA public key and the corresponding R^2 mod n value.
 */
struct Rsquare {
  /**
   * Key to use in calculations.
   */
  const sigverify_rsa_key_t *key;
  /**
   * R^2 mod n.
   *
   * This value must match the result of `calc_r_square`. It can also be used to
   * test `mont_mul` because `mont_mul(mont_mul(R^2, 1, n), 1, n) == 1`.
   */
  sigverify_rsa_buffer_t r_square;
};

/**
 * R^2 mod n for each key in `sig_verify_keys.c`.
 */
constexpr Rsquare kRsquares[kSigVerifyNumRsaKeys] = {
    {
        .key = &kSigVerifyRsaKeys[0],
        .r_square =
            {
                0x801d910d, 0x80b82e51, 0x0693bd8e, 0xe504378f, 0xee7b8dcf,
                0xd46ed96e, 0x2947a90a, 0x32a22331, 0x10450a5d, 0x5191b02a,
                0x5ffe3000, 0xc5b99ee3, 0xe5783783, 0xe6b416da, 0xce7ba8ed,
                0x752bb7b5, 0x47a98315, 0xb31952a1, 0xdac6125f, 0x138a6e2f,
                0xbd918f95, 0x661dda95, 0xfea3ef97, 0xe265c457, 0x12ee497e,
                0x8c54e701, 0xab5f45bc, 0x97d03403, 0x08ecc282, 0xd67c28af,
                0x7680e1d5, 0xafb107b2, 0xa5d7dcc6, 0x78b545a7, 0x5c327005,
                0xe22e96eb, 0xead60b03, 0x62148024, 0xaa2295a2, 0x9a32b8b3,
                0x0bd3f91f, 0xe7d75213, 0x8664627a, 0x6dcc05db, 0x38f9c709,
                0x63b7939d, 0x22ceb26c, 0x5d59488f, 0xe2dac0ef, 0x6cd0d198,
                0x8ed032c9, 0x32ca4a38, 0x26178c9e, 0xa2d5d0a0, 0xaa325002,
                0x8467c351, 0x74695943, 0x2f8720ea, 0x587a3718, 0xd28bd879,
                0xab7c1d12, 0x10299814, 0x47416f21, 0xc6705399, 0x71639c47,
                0x667a4871, 0xc0534500, 0xb1ada3ce, 0x4c3bbfed, 0x88e232bc,
                0x3cbe6cbb, 0x6e3bbb4d, 0x66669fe5, 0x98bde921, 0x43fcba09,
                0xad4b0052, 0x3f725ede, 0xfe73709e, 0xdfb5ddf1, 0xc2a35f88,
                0x91010518, 0x18924c5d, 0xa18e0907, 0xc94a57c2, 0x23127d82,
                0x98eab0c7, 0x1ab48ef3, 0xfd34a853, 0x13d4ebd2, 0x28414f3b,
                0xc27de274, 0xe04f7ea4, 0xffdcf502, 0xf0085483, 0x4738d021,
                0x58adcd5d,
            },
    },
    {
        .key = &kSigVerifyRsaKeys[1],
        .r_square =
            {
                0x0326ea23, 0x46cc29a2, 0xa4d41d01, 0xef0981d2, 0x86beb258,
                0xcedba143, 0xcf27b7e9, 0x432c2e73, 0x57138268, 0x9771655d,
                0xdfd5054d, 0x80a69e65, 0xd8ca5b11, 0x64222c7f, 0x709e703b,
                0x0452dae6, 0x2604c1bf, 0xaf29f6b5, 0x2773bf22, 0x83ab42d4,
                0x34da57f5, 0xfad6aafc, 0xa23f2798, 0x88ab0542, 0x65219ceb,
                0xc5fc703c, 0x9bab047a, 0x48749a33, 0x7067f6d5, 0xfcab7cc9,
                0x878567df, 0x34e07abb, 0x6e5f5247, 0xdd57ed01, 0xd2cdc06e,
                0x0b3c509c, 0x1c94f373, 0xc07a0024, 0x8c92383b, 0x575b4a5c,
                0xd4c086fc, 0x27f19cd7, 0x496d70a4, 0x91d4b3cc, 0x73e34ca2,
                0xa98f4fd4, 0x02ef38ac, 0xfb0a0675, 0xba14f83d, 0x0217c95b,
                0xfc62ca77, 0x310b598c, 0x188e68cd, 0xdbcfdf58, 0xc783c009,
                0xd8abae8c, 0x52d5f747, 0xee2dbda8, 0xd1f5ea87, 0x097f0e5b,
                0x58407a2a, 0xfa880b9b, 0x528d2962, 0xa805f356, 0x9646688e,
                0x2525612b, 0x900cacf4, 0xf844b2a4, 0x04007862, 0x96535db6,
                0x25d03e7f, 0x4460bedf, 0x2961c014, 0x7a25057c, 0xf7bf0721,
                0xfed9dbff, 0x7dfee1e2, 0xa6c7bcd3, 0x2cef3ab5, 0x7c7ffdf8,
                0x4ab94057, 0x04c3cf7c, 0xf1022b35, 0x6cd62eae, 0x9e41a3b6,
                0x8a31357b, 0x40013d2d, 0x5005f7c7, 0xa3ce1d53, 0xfe99692c,
                0x8a612703, 0x2734ccde, 0xd115a702, 0x9b6c042c, 0xdd783f38,
                0x5713d609,
            },
    },
};

class RsquareTest : public testing::TestWithParam<Rsquare> {};

/**
 * Tests that `kRsquares` is not missing any keys.
 *
 * Comparing the result with the expected value for each key provides
 * practically full coverage for `calc_r_square` since it is not called with any
 * other inputs.
 */
TEST(Rsquares, AllKeys) {
  std::unordered_set<uint32_t> ids;
  for (auto const &test_case : kRsquares) {
    ids.insert(sigverify_rsa_key_id_get(test_case.key));
  }

  EXPECT_EQ(ids.size(), kSigVerifyNumRsaKeys);
}

TEST_P(RsquareTest, CalcRsquare) {
  // Uninitialized on purpose.
  sigverify_rsa_buffer_t res;
  calc_r_square(GetParam().key, &res);
  EXPECT_THAT(res.data, ::testing::ElementsAreArray(GetParam().r_square.data));
}

TEST_P(RsquareTest, MontMul) {
  constexpr sigverify_rsa_buffer_t one{1};
  // Uninitialized on purpose.
  sigverify_rsa_buffer_t res1;
  sigverify_rsa_buffer_t res2;

  // mont_mul(R^2, 1, n) = R mod n
  mont_mul(GetParam().key, &GetParam().r_square, &one, &res1);
  // mont_mul(R, 1, n) = 1
  mont_mul(GetParam().key, &res1, &one, &res2);

  EXPECT_THAT(res2.data, ::testing::ElementsAreArray(one.data));
}

INSTANTIATE_TEST_SUITE_P(AllKeys, RsquareTest, testing::ValuesIn(kRsquares));

/**
 * PKCS #1 v1.5 encoded messages used in tests.
 */

/**
 * Message: "test"
 * SHA2-256 hash (little-endian): {0xb0f00a08, 0xd15d6c15, 0x2b0b822c,
 * 0xa3bf4f1b, 0xc55ad015, 0x9a2feaa0, 0x884c7d65, 0x9f86d081}
 *
 * Generated using the `openssl rsautl` command as discussed in
 * sw/device/silicon_creator/keys/README.md.
 */
constexpr sigverify_rsa_buffer_t kEncMsgTest = {
    0xb0f00a08, 0xd15d6c15, 0x2b0b822c, 0xa3bf4f1b, 0xc55ad015, 0x9a2feaa0,
    0x884c7d65, 0x9f86d081, 0x05000420, 0x03040201, 0x86480165, 0x0d060960,
    0x00303130, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0x0001ffff,
};

/**
 * Inputs and expected values for computational tests involving signatures.
 */
struct SigTestCase {
  /**
   * Key to use in calculations.
   */
  const sigverify_rsa_key_t *key;
  /**
   * An RSA signature.
   *
   * Can be generated using the `openssl dgst` command as discussed in
   * sw/device/silicon_creator/keys/README.md.
   */
  sigverify_rsa_buffer_t sig;
  /**
   * sig^2 * R^-1 mod n.
   *
   * This value must match the result of `mont_mul(sig, sig, n)` and can be
   * obtained by computing the above expression, e.g. in python.
   */
  sigverify_rsa_buffer_t sig_mont_mul;
  /**
   * sig^e mod n.
   *
   * This value must match the result of `mod_exp(sig, e, n)`.
   */
  const sigverify_rsa_buffer_t *enc_msg;
};

constexpr SigTestCase kSigTestCases[2]{
    // message: "test"
    {
        .key = &kSigVerifyRsaKeys[0],
        .sig =
            {
                0xeb28a6d3, 0x936b42bb, 0x76d3973d, 0x6322d536, 0x253c7547,
                0x1bfdda9f, 0x597b8193, 0xccac0b02, 0xb3b66a5b, 0xa7880e18,
                0x04846239, 0x4e927eda, 0x37883753, 0x8bc059cd, 0xdc6102d5,
                0xa702185d, 0xf963eec8, 0xfed8f779, 0xc606461b, 0xa5326e90,
                0x87f4ef4b, 0xddaa7f8b, 0xcdae0535, 0x1174dbc8, 0x345db563,
                0x57b9dd37, 0xd6ff9402, 0x1c8077ec, 0x02e76f6f, 0x135797fe,
                0x92ca1d0c, 0x84da4abf, 0xce3f4b43, 0xe3d47def, 0x510ba10e,
                0x9940e174, 0x5c0635bc, 0x8fc7b1d6, 0x9ee042d9, 0x68dc09c7,
                0x30b54030, 0xf2336aa6, 0xaf6535f9, 0x7b1fc0e1, 0xeea50f7c,
                0xe1d2f4b3, 0xa0405640, 0xc035d5b9, 0x34ee81ef, 0xf1460ecf,
                0x943b5734, 0xae5dcd6e, 0x64373ca7, 0x968dd9e5, 0xd1916ff3,
                0x0c4e1ab5, 0x5ba76542, 0x9488cc72, 0x35ef4275, 0x071eef2a,
                0x64516088, 0x42a383fd, 0x477678ee, 0xd1c7c37d, 0x7f55cf49,
                0x24f62205, 0x564dfc4a, 0x8b305ceb, 0x46917278, 0xab9bf3c3,
                0x9a1f6739, 0x188c264e, 0x32c584e9, 0x54d0e1d6, 0x967710a1,
                0x1efe8ffb, 0x299e277a, 0x0ea61f6c, 0xf7845775, 0x78386d10,
                0x66245c4f, 0xfd52953a, 0x955b4b10, 0x6b7d9d30, 0x68fc106f,
                0xbaaebfac, 0x653b64bd, 0x826a3baa, 0x98703747, 0x6ee930ec,
                0xacbb94d8, 0xcede8d12, 0xa17b3cb0, 0xa520fe81, 0x84df2df5,
                0x4f97181e,
            },
        .sig_mont_mul =
            {
                0x8bce09dc, 0x8117aaf5, 0x75fb01e0, 0x622d893a, 0x46d42e04,
                0xc6b19ba4, 0xa7c09e75, 0x97793a53, 0xf8b64e2b, 0x2fc2b08e,
                0xe3e5fbff, 0x2a84abbd, 0x5c49ff33, 0xf9d60b9c, 0x0dc15132,
                0xc23f4cdf, 0xd6e95f5f, 0x3f9c847d, 0x0234939c, 0x7326725d,
                0x0da0d7c8, 0xc256ddcc, 0xd1b5f8e4, 0xdd8c5da0, 0xfed1e177,
                0x25ac7c96, 0x54b3efb6, 0x703ca0f1, 0x68974bea, 0x73b62f01,
                0x5950cd02, 0x0a430e77, 0xca92ac5c, 0xe7d45063, 0x7b45e172,
                0x1bcb281a, 0x4a104046, 0x1887ccbc, 0xc85432b9, 0xe577bf0c,
                0x483dfa54, 0x0f074e63, 0x4be1fe15, 0xca2fabdd, 0xd9d1a6d8,
                0x2502bf8c, 0x9687dbd4, 0xa9b0dcf7, 0x90b2e7ee, 0x4af1e395,
                0x4e1d42e7, 0x799a8905, 0x28149ec0, 0xeb6a3bab, 0xfd74060e,
                0x7cc5574c, 0xf844c82f, 0xac3a4b25, 0x60fd00ff, 0xc5649499,
                0xb306c551, 0x33bd6825, 0x6cdf5a41, 0xa80cb818, 0x60bc2349,
                0x3b8c1533, 0x4098f3d0, 0xb07c04b1, 0x47f63388, 0xbe0f7133,
                0xd697b7b5, 0xb0d075fb, 0x0ab2ee07, 0x8593da0a, 0xfbcd5b45,
                0x61ce5320, 0xce82719c, 0x9ce114bc, 0xa82b12da, 0x1cb971a4,
                0xf77d1c06, 0xb6bb905d, 0x6fd9a1f1, 0xefbfe75e, 0x7f648024,
                0x29921282, 0x1d0c9025, 0x48dab624, 0xbbc6619e, 0xa38f9b32,
                0xf4f8d082, 0xfdf8f227, 0x177ffebb, 0x7fc84cb3, 0xb8d739f2,
                0x5992c1c0,
            },
        .enc_msg = &kEncMsgTest,

    },
    // message: "test"
    {
        .key = &kSigVerifyRsaKeys[1],
        .sig =
            {
                0xb13844fa, 0x9c7622d8, 0xda09bdc4, 0x79fde5c6, 0x7037a98b,
                0x4d53a5cf, 0xabd7e9e4, 0x8456c575, 0x1f1fc5f6, 0x7870e2d5,
                0x96a488c2, 0x7aa2263c, 0xbe5dbcf1, 0x34a6b2ff, 0x51bd23fa,
                0xef582d6d, 0x52d0e2fa, 0x586c6b2f, 0x0aa1e7d0, 0x0d1f8a33,
                0xf95e28bc, 0x70f13b45, 0x548740b0, 0x42be7f0d, 0x4254ac6f,
                0xb7363b68, 0x48f1c461, 0x06b8f936, 0xd3274353, 0x121219e4,
                0x98d8e770, 0x39e1bb17, 0x1a005ad4, 0x673985f4, 0x6f2cfd4a,
                0xba537c5f, 0x1ca6bdad, 0x5e7bdb7d, 0x9b6783bd, 0xf3a1e998,
                0xa5dc56f6, 0x149d6bb5, 0x9437917a, 0xfeb89880, 0x6e6ce5f9,
                0x07bece66, 0xaab327ae, 0x1ff13a9e, 0x35e3b280, 0x645b636a,
                0x34628104, 0xda8148ee, 0x95d22ce1, 0x78f4e1a0, 0xec9bdf2e,
                0x42fc69d0, 0x4b8e5244, 0x192a0454, 0x7bfd31dc, 0x09a07d77,
                0x2a3c745b, 0x8d5deeb7, 0xb539505c, 0xd5352a21, 0x22fd9774,
                0x6fd4f48f, 0x60d2c5e9, 0x9292c725, 0x035797d8, 0x8bbb8d02,
                0x977bdd02, 0x2da179b2, 0xa9779cc9, 0x13c5fe29, 0x607c3673,
                0x8e52aeca, 0x6fd9ea3a, 0x5915a281, 0x69dc74c2, 0x162207fb,
                0x1efa0497, 0x0a9e1a61, 0x3542ac58, 0x885d5d5e, 0x29623b26,
                0x14cbc783, 0xa2f9511e, 0xfcb8986f, 0x6b7ca8d8, 0xde4c53b2,
                0x4f8fd997, 0x2eded334, 0xe9d492dd, 0xd0751bc1, 0x9077d8cd,
                0x5563ec91,
            },
        // Note: This is not the least non-negative residue of sig^2*R^-1 mod n.
        .sig_mont_mul =
            {
                0x5a6fe519, 0x7f5b040d, 0x363568d4, 0xf199dc93, 0x0b88ca6a,
                0xa8dc9812, 0xba42c5e1, 0x3c7e0b39, 0x02142e93, 0x517784b3,
                0x442c3a51, 0xdf015f60, 0xc1168915, 0x85fd610e, 0xcf28e92f,
                0xb6397f84, 0x4a263275, 0x3419dd89, 0x1ffa6455, 0xf13b29be,
                0xf567fc9f, 0x3592d2e6, 0xf2d5cdfd, 0x62ffa92d, 0x05fd99f0,
                0xde88fbc2, 0x32f074d2, 0x5773eac8, 0xefb84135, 0x7ec58441,
                0xaa2d38c6, 0xd14bdab5, 0xc67281b9, 0xeab5ff55, 0xfd71e3c8,
                0x758b576c, 0xf28f53fb, 0x454f996a, 0x08734870, 0xb7f17b3e,
                0x33a58eab, 0xbb6a4b69, 0xe3ed75b5, 0x83a05765, 0x3dcc3502,
                0xe34a0bc9, 0x33146f45, 0x762645b2, 0xdfda8a41, 0xd05f66db,
                0x4367ffb2, 0xceec2aa3, 0x791f3c44, 0x83e7e788, 0x7b8b8b74,
                0x1bd3032d, 0x111ba6d1, 0xd075cc96, 0x3aebbe0f, 0xc928abf1,
                0x87090f1f, 0x7d937d59, 0xb030bd9d, 0xdb397398, 0x6ea6fc58,
                0xcae53095, 0xc1a23d24, 0x814d9abc, 0x8e73da7e, 0x84924ef0,
                0xd82cee3b, 0xd46dd52f, 0x21cf7a77, 0xba8e9f48, 0x6eac3832,
                0x59eb8346, 0xf4944cde, 0x99b5fa50, 0xa6803df2, 0xa047f7cd,
                0x8caff8bd, 0x9b171d90, 0x7a5f94f2, 0xfe787dbd, 0x30b6dba0,
                0x59aff83b, 0xc63302d1, 0x6f34350f, 0xc533c9ea, 0x44833e9d,
                0xf3720531, 0xbc55560c, 0xf6ac39fb, 0xfaa3ed21, 0xfb77f6ed,
                0xb365e0b4,
            },
        .enc_msg = &kEncMsgTest,
    },
};

TEST(SigTestCases, AllKeys) {
  std::unordered_set<uint32_t> ids;
  for (auto const &test_case : kSigTestCases) {
    ids.insert(sigverify_rsa_key_id_get(test_case.key));
  }

  EXPECT_EQ(ids.size(), kSigVerifyNumRsaKeys);
}

class MontMul : public testing::TestWithParam<SigTestCase> {};

TEST(MontMul, SmallNumbers) {
  // Values are from ex. 14.35 in Handbook of Applied Cryptography except for
  // m' and expected result are computed for base 2^32 and R = 2^3072 (96 base
  // 2^32 digits):
  // - m' = -m^-1 mod b = 3837733825
  // - R^-1 mod m = 72136
  // - x * y * R^-1 mod m = 55123
  constexpr sigverify_rsa_buffer_t x{5792};
  constexpr sigverify_rsa_buffer_t y{1229};
  constexpr sigverify_rsa_key_t key{
      .n = {72639},
      .n0_inv = 3837733825,
      .exponent = 3,
  };
  constexpr sigverify_rsa_buffer_t exp_res{55123};
  // Uninitialized on purpose.
  sigverify_rsa_buffer_t act_res;

  mont_mul(&key, &x, &y, &act_res);

  EXPECT_THAT(exp_res.data, ::testing::ElementsAreArray(act_res.data));
}

TEST_P(MontMul, Sig) {
  sigverify_rsa_buffer_t res;
  mont_mul(GetParam().key, &GetParam().sig, &GetParam().sig, &res);
  EXPECT_THAT(res.data,
              ::testing::ElementsAreArray(GetParam().sig_mont_mul.data));
}

INSTANTIATE_TEST_SUITE_P(AllCases, MontMul, testing::ValuesIn(kSigTestCases));

class ModExp : public testing::TestWithParam<SigTestCase> {};

TEST_P(ModExp, EncMsg) {
  sigverify_rsa_buffer_t res;
  EXPECT_EQ(sigverify_mod_exp_ibex(GetParam().key, &GetParam().sig, &res),
            true);
  EXPECT_THAT(res.data, ::testing::ElementsAreArray(GetParam().enc_msg->data));
}

TEST(ModExp, BadExp) {
  // Exponent = 0
  constexpr sigverify_rsa_key_t bad_key{};
  sigverify_rsa_buffer_t empty;

  EXPECT_EQ(sigverify_mod_exp_ibex(&bad_key, &empty, &empty), false);
}

INSTANTIATE_TEST_SUITE_P(AllCases, ModExp, testing::ValuesIn(kSigTestCases));

}  // namespace
}  // namespace rsa_verify_unittest
