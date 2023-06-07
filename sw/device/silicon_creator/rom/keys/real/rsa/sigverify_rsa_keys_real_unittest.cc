// Copyright lowRISC contributors.
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

const RsaVerifyTestCase kRsaVerifyTestCases[7]{
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
                0x98426123, 0x31711c08, 0x7e7c34bd, 0x6cdaa964, 0xf84d18c3,
                0x7e2b974a, 0x13463262, 0x4a42c6bb, 0xd605e124, 0xa6936221,
                0x4be5c101, 0x2bf826f9, 0x3e0dad90, 0xa7c28ff0, 0xf129de12,
                0x564bb45b, 0x74da744a, 0x6b4f9b2c, 0xbd8aaed9, 0x45943745,
                0x3b363333, 0xaab22683, 0x54c28d79, 0xb68d104c, 0x8a9cb88a,
                0x77563e8c, 0x9e55346b, 0xc1cb14d7, 0x7f6bbf28, 0x334728d0,
                0x1d2b36d7, 0x0f363858, 0x5268dc7f, 0xbe9259e2, 0x619fcd3b,
                0xc6582877, 0x2705f11d, 0xb053df86, 0x9d889244, 0xb6d48747,
                0x1f1eddc3, 0x30bfc4ff, 0x7dfddd9c, 0x116af92e, 0x0c64642f,
                0x9ad9cef3, 0xfbe24aca, 0xf7d0a6f8, 0xbc31ca40, 0xbf4f17b3,
                0xf2998301, 0x953d9e5a, 0xff1e2a0a, 0x5b2e8b5f, 0xae4b234d,
                0xa1559f1b, 0x569825b0, 0xc6aca403, 0x4befc159, 0x06a19d4d,
                0x56ee54ab, 0xb98b0224, 0x68867ff4, 0xb2046446, 0x86a36399,
                0x468449cd, 0x9a573b52, 0x05401e18, 0x2e8eb69b, 0x824195cf,
                0xea0cea83, 0x6b9b3be3, 0x4a3b0193, 0x1a0824a1, 0xe139969d,
                0x839692e0, 0x991419b5, 0xcda83ef4, 0x37f36748, 0xedd9f78d,
                0xf95cf43d, 0x9522e5f4, 0xa42d0310, 0xc2fbb256, 0x0c878ae1,
                0xa9b43324, 0x8133a479, 0xa2d15638, 0xabe9a4bf, 0xf34aec69,
                0x439d91a6, 0x79a8232f, 0xcc9a96ac, 0xcb8bb7cf, 0xedc4a25b,
                0xafa8cc16,
            },
    },
    {
        .key = &kSigverifyRsaKeys[2].entry.key,
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
        .key = &kSigverifyRsaKeys[3].entry.key,
        .sig =
            {
                0xa1bc3e16, 0xa9857e45, 0xf530e89a, 0xf7005dd9, 0x6d35d2ed,
                0x7c1f8cb6, 0xf479c95f, 0x88f72146, 0x433b522d, 0xb052c73d,
                0x5c7a4eda, 0xa89a070f, 0xa2fc08fb, 0x0fb7f139, 0x30f0e2db,
                0xaad0c189, 0x169890a0, 0xb36ebff7, 0x8dfe3ff2, 0xa0ff6b59,
                0xd045b019, 0x3c051e23, 0xa85e3b95, 0x82153734, 0x18a6c919,
                0x00eb6c71, 0x1f89d834, 0x51c2cd93, 0xef3a61a4, 0x54af904c,
                0x28a05b61, 0xc27c1280, 0xb08dfc35, 0xee9ae636, 0x52e1f31a,
                0x37180795, 0xae99427c, 0x18c37ba7, 0x906d4b53, 0xb75f17e8,
                0x5867669d, 0xdc3ed552, 0x47f37fbc, 0xae23d928, 0x4b0cb4d3,
                0x6d0aba20, 0x12145301, 0xf6d34bbd, 0xaa2fab86, 0x5ed0f954,
                0xb3ba285b, 0x265a25b4, 0x2c8a3ae0, 0x536dca17, 0xa5a5b11a,
                0x91ad132c, 0xa206c6fc, 0x13dc89dc, 0x8de4efc6, 0xe627101b,
                0xceb04a7e, 0xf54a9f53, 0x65ce83a5, 0xe8ebb0f7, 0x0d05e631,
                0x554fe096, 0xe8ef42b1, 0x649e000c, 0xb0d2a52d, 0x24979fde,
                0xf2268049, 0x0d3c7a50, 0x8ec0e154, 0x1e11270e, 0xa48fef6c,
                0x2eb32d13, 0x3e772ad7, 0x30f357a1, 0x03f8bc26, 0x12f43863,
                0xe05a117d, 0xc6e2064f, 0x923f4034, 0x6b18c12a, 0x9f6261d2,
                0xf19e16ea, 0x83c94201, 0x1c5fc049, 0xa1d41076, 0x546be2bb,
                0x3c1b7c5e, 0x2a95751d, 0xebc6cfdb, 0xefa06bb0, 0xb1bf0f5d,
                0x21a3b4e2,
            },
    },
    {
        .key = &kSigverifyRsaKeys[4].entry.key,
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
    {
        .key = &kSigverifyRsaKeys[5].entry.key,
        .sig =
            {
                0x2d6284da, 0x16f335b5, 0x10bc1739, 0x478ec8e8, 0x7e68812b,
                0x4874de7f, 0x085829b5, 0x5b2a08d2, 0xed6942da, 0x8545e1f2,
                0xec15b163, 0x68ee75ce, 0x44ca36ab, 0x5cb1cc4e, 0x3bec1dd3,
                0x58d98020, 0x3f8b1456, 0x9fc12899, 0x24127e11, 0x4c8ebb21,
                0x6aa63bae, 0x18412114, 0x63b08a7c, 0x347aafe8, 0xc7e12344,
                0x20ea10fb, 0x367f9b8f, 0x791931be, 0xb42b4d2f, 0xc92508f2,
                0x1691e652, 0xe362fdc7, 0xa0123e7f, 0xf069e5c3, 0x0dcd22ed,
                0x703d7adc, 0xc940814c, 0x403a8dae, 0x9f5e9073, 0xf23076c2,
                0xfac0d40c, 0x6f61f6c3, 0xfdf079f7, 0xa2dd7d0f, 0x3aff56b0,
                0x74b8fb05, 0xbec08672, 0x06e1a873, 0x30bbe785, 0x23c9beae,
                0x3a2802b7, 0xcfe58601, 0x981668ef, 0x1ba01c6d, 0xa02f24ac,
                0x51f6d4d1, 0x4aebe5d6, 0xc95fca07, 0x1c10e32f, 0x17a1c137,
                0x7e74269a, 0x1e7d7f00, 0xfa4b4fe1, 0xeec867f4, 0x4c66a45e,
                0x9e01e5ee, 0xfb69c3a1, 0x7455923e, 0xcecc66bf, 0xd34d73c0,
                0xe40ad9da, 0x2fff57c7, 0xcc637495, 0x9ff2e5f3, 0x0d076678,
                0x9eec893f, 0x2d727648, 0xac9bdb1c, 0x89c72b19, 0xd2cb459e,
                0xf37d4661, 0x355960f1, 0xcb69ebd3, 0x66eac3ee, 0x6b2fa06c,
                0x066d62fa, 0x7d346b81, 0xc22fae4b, 0xc892173f, 0x39b18800,
                0xdc993c2c, 0xa0b56e75, 0xe17f341d, 0x83837fad, 0x552aa479,
                0x26e87fa1,
            },
    },
    {
        .key = &kSigverifyRsaKeys[6].entry.key,
        .sig =
            {
                0x8e17e217, 0xab7b5da5, 0xbec5200a, 0x860200d1, 0x23061759,
                0x0b46b6c8, 0x2f748bed, 0x80096f7a, 0x860a6c2e, 0xeaa9ddf2,
                0x5d41112b, 0xcb0149c3, 0x6787381e, 0xe7c9b9c9, 0x0c35b7a7,
                0x27422f9b, 0x39bc063e, 0xca9a1cbb, 0x066b8c38, 0xf381f1df,
                0x9ccd4e99, 0xd40baba4, 0x6cc07d9f, 0x2e9ccd17, 0x5e669736,
                0x37a7af00, 0xb4bb5658, 0x45df45b4, 0xeff42185, 0x257d4726,
                0xdfe65079, 0x61e6f6ee, 0xe505744f, 0x5be57d26, 0x03634650,
                0x72d47ae4, 0x6cc8e3fe, 0x469985f2, 0xba52886f, 0xd758ed43,
                0x0e828f2a, 0x9051595b, 0x9a0aca8c, 0x04103076, 0x7577073c,
                0xf09f337d, 0x84b4b385, 0x6b1fad61, 0x6c86f256, 0x5f7c2375,
                0x3fbf1b35, 0x33eaf444, 0x9179d234, 0x1a9310b8, 0xd56d9ca8,
                0x6e3a72bd, 0x2b291910, 0xb39e1dc9, 0xb8303d58, 0x6ec3d5ea,
                0x54bd28af, 0xc77de6df, 0xc9408ed8, 0x33f403cd, 0x952fb8e1,
                0x3b3731ca, 0x95e6c0c5, 0xc8f36529, 0x032c7f50, 0xfaeab17e,
                0xa862138e, 0x46ac140b, 0x4dfab53e, 0x0bdcea44, 0xa099f321,
                0x1af9408d, 0x97a3d107, 0xdf22092a, 0xe0005b0e, 0xcb8ed170,
                0x36e37e76, 0x9074e16b, 0x2d4cbabb, 0x596e7abc, 0x08871a9c,
                0xe8935e73, 0xf9c31b75, 0x8124ea8b, 0x0c0308c2, 0x315276cd,
                0x782b823d, 0x038a8338, 0x4e7912a8, 0x131f3f63, 0x4eb7c8b1,
                0x64a0be96,
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
