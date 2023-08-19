// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"

#include <unordered_set>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

namespace sigverify_mod_exp_ibex_unittest {
namespace {

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
  const sigverify_rsa_key_t key;
  /**
   * An RSA signature.
   *
   * Can be generated using the `openssl dgst` command as discussed in
   * sw/device/silicon_creator/keys/README.md.
   */
  sigverify_rsa_buffer_t sig;
  /**
   * sig^e mod n.
   *
   * This value must match the result of `mod_exp(sig, e, n)`.
   */
  const sigverify_rsa_buffer_t *enc_msg;
};

// The keys below do not need to be kept in sync with the actual keys used in
// boot stages since we have separate tests for each boot stage.
constexpr SigTestCase kSigTestCases[1]{
    // message: "test"
    {
        // sw/device/silicon_creator/rom/keys/fake/test_key_0_rsa_3072_exp_f4.public.der
        .key =
            {
                .n = {{
                    0x5801a2bd, 0xeff64a46, 0xc8cf2251, 0xa7cd62cb, 0x634a39c2,
                    0x55c936d3, 0x463d61fc, 0x762ebbaa, 0x01aadfb2, 0x23da15d1,
                    0x8475fdc6, 0x4ec67b7b, 0xe9364570, 0xd23ec7c7, 0x98038d63,
                    0x5688a56b, 0x68037add, 0xb20ff289, 0x9d96c1ce, 0xbac0b8cd,
                    0xead33d0b, 0x195f89c8, 0xd7dc110e, 0xf5bccc12, 0x8dfa33dc,
                    0xedc404d2, 0x74ef8524, 0x9197c0c8, 0x79cc448e, 0x4c9c505d,
                    0x4a586ad7, 0xe2d0f071, 0x589f28c2, 0x2ca7fc22, 0x0354b0e2,
                    0xefb63b44, 0x33a75b04, 0x9e194454, 0x1b4b2cde, 0x8e3f78e0,
                    0x5260877c, 0x05685b72, 0x4868ad4e, 0x10303ac9, 0x05ac2411,
                    0x5e797381, 0xd5407668, 0xe3522348, 0xa33134f8, 0x38f7a953,
                    0xd926f672, 0x136f6753, 0xb186b0ab, 0x5ccab586, 0x61e5bf2e,
                    0x9fc0eebb, 0x788ed0bd, 0x47b5fc70, 0xf971262a, 0x3b40d99b,
                    0x5b9fd926, 0xce3c93bf, 0xd406005e, 0x72b9e555, 0xc9b9273e,
                    0xfcef747f, 0xf0a35598, 0x2761e8f6, 0xec1799df, 0x462bc52d,
                    0x8e47218b, 0x429ccdae, 0xe7e7d66c, 0x70c70b03, 0x0356c3d2,
                    0x3cb3e7d1, 0xd42d035d, 0x83c529a3, 0x8df9930e, 0xb082e1f0,
                    0x07509c30, 0x5c33a350, 0x4f6884b9, 0x7b9d2de0, 0x0f1d16b3,
                    0x38dbcf55, 0x168580ea, 0xc2f2aca4, 0x43f0ae60, 0x227dd2ed,
                    0xd8dc61f4, 0x9404e8bc, 0x0db76fe3, 0x3491d3b0, 0x6ca44e27,
                    0xcda63719,
                }},
                .n0_inv =
                    {
                        0x9c9a176b,
                        0x44d6fa52,
                        0x71a63ec4,
                        0xadc94595,
                        0x3fd9bc73,
                        0xa83cdc95,
                        0xbe1bc819,
                        0x2b421fae,
                    },
            },
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
        .enc_msg = &kEncMsgTest,
    },
};

class ModExp : public testing::TestWithParam<SigTestCase> {};

TEST_P(ModExp, EncMsg) {
  sigverify_rsa_buffer_t res;
  EXPECT_EQ(sigverify_mod_exp_ibex(&GetParam().key, &GetParam().sig, &res),
            kErrorOk);
  EXPECT_THAT(res.data, ::testing::ElementsAreArray(GetParam().enc_msg->data));
}

INSTANTIATE_TEST_SUITE_P(AllCases, ModExp, testing::ValuesIn(kSigTestCases));

}  // namespace
}  // namespace sigverify_mod_exp_ibex_unittest
