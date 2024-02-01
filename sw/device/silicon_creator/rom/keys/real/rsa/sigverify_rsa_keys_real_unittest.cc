// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <array>
#include <cstring>
#include <limits>
#include <numeric>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_rsa.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "otp_ctrl_regs.h"

namespace sigverify_keys_unittest {
namespace {
using ::testing::Return;

TEST(Keys, UniqueIds) {
  std::unordered_set<uint32_t> ids;
  for (size_t i = 0; i < kSigverifyRsaKeysCnt; ++i) {
    ids.insert(sigverify_rsa_key_id_get(&kSigverifyRsaKeys[i].entry.key.n));
  }

  EXPECT_EQ(ids.size(), kSigverifyRsaKeysCnt);
}

/**
 * An implementation of the Euclidean algorithm since we can't use c++17's
 * `std::gcd()` yet.
 */
uint32_t Gcd(uint32_t a, uint32_t b) {
  while (b != 0) {
    std::tie(a, b) = std::make_tuple(b, a % b);
  }
  return a;
}

TEST(KeysStep, IsCorrect) {
  if (kSigverifyRsaKeysCnt > 1) {
    EXPECT_LT(kSigverifyRsaKeysStep, kSigverifyRsaKeysCnt);
    EXPECT_EQ(Gcd(kSigverifyRsaKeysStep, kSigverifyRsaKeysCnt), 1);
  }
}

// Note: The test cases below test sigverify using ROM keys. They have some
// overlap with sigverify_mod_exp_ibex unit tests but this way we don't have to
// worry about keeping the keys used in those tests in sync with ROM keys.

/**
 * Message and digest used in tests.
 *
 * The digest can be obtained using:
 * ```
 * echo -n "test" | openssl dgst -sha256 -binary | \
 *    xxd -p -c 4 | tac | sed 's|.*|0x&,|'
 * ```
 */
constexpr hmac_digest_t kDigest = {
    .digest =
        {
            0xb0f00a08,
            0xd15d6c15,
            0x2b0b822c,
            0xa3bf4f1b,
            0xc55ad015,
            0x9a2feaa0,
            0x884c7d65,
            0x9f86d081,
        },
};

/**
 * Keys and signatures used in tests.
 *
 * These can be generated using the `openssl dgst` command as discussed in
 * sw/device/silicon_creator/keys/README.md.
 */
struct RsaVerifyTestCase {
  /**
   * Signer's RSA public key.
   */
  const sigverify_rsa_key_t *key;
  /**
   * Signature to be verified.
   */
  sigverify_rsa_buffer_t sig;
};

const RsaVerifyTestCase kRsaVerifyTestCases[3]{
    // message: "test"
    // The signatures were generated with `hsmtool`:
    // hsmtool -t <token> -u user -p <pin> exec earlgrey_test_signatures.hjson
    //
    // Then, each of the signature files was post-processed to the proper
    // word size and endianess via:
    // cat <sig-file> | xxd -p -c 4 | tac | sed 's|.*|0x&,|'
    {
        .key = &kSigverifyRsaKeys[0].entry.key,
        .sig =
            {
                0xa341663d, 0x2e75cbe9, 0x1f9779eb, 0xa2e68398, 0x2190e3e5,
                0xfb5148ba, 0xb4608a88, 0xe2ee44e2, 0x07e96270, 0x0f27ac91,
                0x386d0217, 0x83d9c90e, 0xee55f78a, 0x9400a7bc, 0x213c9012,
                0xe7c64707, 0x89c700fe, 0x5e3767bf, 0x4773fdba, 0xb3080a9b,
                0x29538a6b, 0x3198dad4, 0xb186ed12, 0x4ddb679c, 0xa52b33e6,
                0xe7ea6d97, 0x5114d3e2, 0xc13ace16, 0xbfa700f8, 0x2ef9bce5,
                0xbd8a89b7, 0x6df00a61, 0xbf9b84b1, 0x2b065f0f, 0xbd371925,
                0x303f1ce8, 0x8a29a731, 0xd26b6aea, 0x80b87a20, 0x24a3f886,
                0x550a7242, 0x502ff153, 0x6c03d669, 0x16ce40ff, 0xfdb73326,
                0x98abed1e, 0x49441285, 0x1a830fe3, 0xe17d396f, 0xacd2d412,
                0xd4c12110, 0x16a5bae8, 0x9ddebff9, 0x2d512913, 0x9a7e743c,
                0xdb0dd071, 0x7e60af70, 0xbd4790b3, 0xb623a5e2, 0xa3f80188,
                0x816d0dbf, 0xb3fc4945, 0x5663a071, 0x7a794a05, 0xb3b1a815,
                0x81c6d27a, 0x5eb7b8b2, 0xe6691b2e, 0x1c992b7f, 0x983c4de8,
                0xec6c3717, 0x1ec6b343, 0x1c4dd31e, 0x535a5b75, 0x38d8e1ad,
                0xff37ded4, 0xa5b29bea, 0x28c84128, 0x5101a3b5, 0xfb5e886a,
                0x824196de, 0x8afe9c1b, 0x878f9076, 0xa3fdc7d5, 0xdda9dfba,
                0xbc968d82, 0xc19547ec, 0xdb92ae51, 0x308e0272, 0x9db10532,
                0xc7b30e50, 0xdb115002, 0x4039d5f8, 0x2391fbca, 0x6e28f1dc,
                0x620f67cb,
            },
    },
    {
        .key = &kSigverifyRsaKeys[1].entry.key,
        .sig =
            {
                0x94877207, 0x5d4cb48b, 0xb55755f1, 0xb89f089c, 0x5f034721,
                0x37ecc0b2, 0xb082efaa, 0xe4db4086, 0xaca7253f, 0xcaa29708,
                0x29bad393, 0xd9de7c55, 0x7aae6647, 0xf077ab52, 0x61c7609a,
                0xb210ec71, 0xc4ea91e0, 0x79b40002, 0x958ba57e, 0xa4388050,
                0x6cd2ff6f, 0x104390a5, 0x7fb5331f, 0xfd6161e2, 0x447e4502,
                0xecedd83e, 0x27a94d68, 0x74cc80d1, 0x646e06bd, 0xc5191441,
                0x25eccb37, 0x82f39563, 0x571b0038, 0xfde34012, 0xbf54f186,
                0xc8e77b72, 0xe48bd21e, 0xd1113820, 0xae78d99a, 0x35b76445,
                0x767e6f87, 0xa6245115, 0x653f95c4, 0x27dd148d, 0x1fa34d52,
                0xb81de2e8, 0x1e755949, 0x08fc25d7, 0x5f750bbc, 0x4a04277a,
                0x12ea37a4, 0x03653d9d, 0xdf403afa, 0x9eb6c17d, 0xff697b83,
                0x94bb056a, 0xe4904444, 0xd3a871d3, 0x606146b6, 0x85fc2013,
                0xf1c55bec, 0x2fc64c40, 0xc30418f9, 0xf87d0e6a, 0xb481f78e,
                0x15bd697c, 0x81195b2f, 0x5954d504, 0x461a9b9b, 0x2c862b8f,
                0x64eee7bb, 0x361b6a96, 0xf35b9b2c, 0xb733c1b2, 0xe0142822,
                0x537f623b, 0xcd319129, 0x1b76d165, 0xa9d983cd, 0xaa6f4268,
                0x19291ea7, 0xc9efe960, 0x7e238215, 0xe451c22c, 0x16e80777,
                0xad5682aa, 0x56aba0be, 0x1c453a23, 0xe5def72d, 0xa5af4ddd,
                0xedfaaa14, 0x47816713, 0x41f1cf47, 0x401bb2e5, 0x1a7fd91e,
                0xc8fe71f4,
            },
    },
    {
        .key = &kSigverifyRsaKeys[2].entry.key,
        .sig =
            {
                0x1f1050fb, 0xc5fe7c43, 0x00483e53, 0x1189d008, 0xbb949c7b,
                0x143ff656, 0xa6999739, 0xc0d3081a, 0x37e0ade7, 0x927a1a76,
                0x96b82fdf, 0x0838b7d5, 0xbd135078, 0xe9d29a20, 0x85460385,
                0xeb611296, 0xe9b3a2ac, 0x48906390, 0x89fe4d11, 0xbf0ded56,
                0x2325bdec, 0xf15ed0d4, 0xa59417ce, 0x302f49f5, 0x09eb7b97,
                0x50331aff, 0x52879e16, 0x2c54aff6, 0xd7835b81, 0x42a9c6ae,
                0x085309b9, 0x1206d7b7, 0xa9496c16, 0xf7191c31, 0xfc60bd69,
                0x461b2af0, 0x3ca9ca90, 0x8872136e, 0x41f0bb74, 0xf59de85b,
                0xaa6c84d5, 0xcdf96b7a, 0x08619fff, 0x08ead10e, 0x923b7404,
                0x438f1f58, 0x730795cb, 0xca4f8009, 0x7137ec96, 0xb8e748e3,
                0x00881e99, 0xf8527ae3, 0x2964ffb0, 0xda06542f, 0x8518c70b,
                0x6f238cf1, 0x9d37c5b9, 0xe61c1013, 0x37cbea8a, 0xfa54d23c,
                0xfe46e1bd, 0x4876635d, 0xef2b6a31, 0xa3f9c686, 0x202072be,
                0x84565ede, 0xf0c3e851, 0x947a4fcf, 0x42d27968, 0x0f50144f,
                0xb4c1895e, 0xeb0036cd, 0x68a39f73, 0x43636978, 0x0ad91f64,
                0xfa4385ec, 0xdc063024, 0xdd87072e, 0x88912bf1, 0xdf85a32a,
                0x7f4711a4, 0xe9ac1f63, 0xea38b4cf, 0x15a5ca6c, 0x616a6357,
                0x2505ebee, 0xf31e9396, 0x2cd98068, 0xcebfd345, 0x5362697e,
                0xa5d119b6, 0xcb81b3de, 0x2997d0b2, 0x19473f58, 0x8f885459,
                0x607deda0,
            },
    },
};

TEST(RsaVerifyTestCases, AllKeys) {
  std::unordered_set<uint32_t> ids;
  for (auto const &test_case : kRsaVerifyTestCases) {
    ids.insert(sigverify_rsa_key_id_get(&test_case.key->n));
  }

  EXPECT_EQ(ids.size(), kSigverifyRsaKeysCnt);
}

class SigverifyRsaVerify
    : public rom_test::RomTest,
      public testing::WithParamInterface<RsaVerifyTestCase> {
 protected:
  rom_test::MockOtp otp_;
};

TEST_P(SigverifyRsaVerify, Ibex) {
  EXPECT_CALL(
      otp_,
      read32(
          OTP_CTRL_PARAM_CREATOR_SW_CFG_SIGVERIFY_RSA_MOD_EXP_IBEX_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  uint32_t flash_exec = 0;
  EXPECT_EQ(sigverify_rsa_verify(&GetParam().sig, GetParam().key, &kDigest,
                                 kLcStateProd, &flash_exec),
            kErrorOk);
  EXPECT_EQ(flash_exec, kSigverifyRsaSuccess);
}

INSTANTIATE_TEST_SUITE_P(AllCases, SigverifyRsaVerify,
                         testing::ValuesIn(kRsaVerifyTestCases));

}  // namespace
}  // namespace sigverify_keys_unittest
