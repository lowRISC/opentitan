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
    {
        .key = &kSigverifyRsaKeys[0].entry.key,
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
    },
    {
        .key = &kSigverifyRsaKeys[1].entry.key,
        .sig =
            {
                0xef57ff30, 0x95aab770, 0x1111a0e3, 0x972d0115, 0x72caf9a6,
                0x8322c9b7, 0xa627ef11, 0xeaf1a8ef, 0x5b231edf, 0x3bac5a7d,
                0x7f6dade1, 0x121962ed, 0x3cbd4b08, 0xbb8ef889, 0x7e45411b,
                0x92eecfce, 0xfaacdedc, 0x3a502da1, 0x9d2a2390, 0x78237336,
                0x53c6e775, 0xe2e5af7a, 0x748eb8fb, 0x549807ca, 0x8b50584f,
                0x9692c057, 0xbfa217da, 0xf5b4d228, 0x867c8492, 0xcf4700d2,
                0xeab74029, 0x2939dff6, 0x6e0e32e5, 0x9e469bc6, 0xf8782d95,
                0x3d30f149, 0xfb9a4784, 0xb433bfc4, 0x8d950344, 0xa972b015,
                0xc508e1ee, 0x4f985d05, 0x9d0a2442, 0xad37ac1d, 0x84c73837,
                0x22bd3c8b, 0x48d1b41a, 0x71b45377, 0x32fe54c0, 0x5eb819da,
                0x61ceeca4, 0x6f0bb173, 0x2a7df150, 0x4130bd1c, 0xaca5135f,
                0x42341c8e, 0x05aeb721, 0x864810e0, 0x62904801, 0xc492d5b1,
                0x6cdea196, 0x725d4037, 0xa1d4d5d4, 0xd887b7ef, 0x0dc4b374,
                0x5edb303e, 0x906051e0, 0x5e06e51f, 0x9db997dc, 0x6007d0a3,
                0xeb90cb2d, 0x0016a74d, 0x3d88e6ed, 0xa7885167, 0xf1cfd78c,
                0xe82411f3, 0x9cc3f0d2, 0x753d9e81, 0xb97140c7, 0x7d7888a1,
                0xaed7688d, 0x0febbfe3, 0x84172081, 0x6b7ac93a, 0xff938ab6,
                0x64e79866, 0xcc14c772, 0x1986d268, 0xfee820ac, 0xe80d0882,
                0x1dce7b62, 0xdcf4192f, 0xbf4823ed, 0xf639ba95, 0xb3d5a2cf,
                0x8968a8a9,
            },
    },
    {
        .key = &kSigverifyRsaKeys[2].entry.key,
        .sig =
            {
                0x3106a8c5, 0xb7b48a3a, 0xb06af030, 0x9dca44b1, 0x55eaa90a,
                0xf92f47ff, 0x9580f0bf, 0x30b50b5d, 0xcc5fd284, 0x5f176cf5,
                0xacc49b93, 0x138a4b2d, 0x9c38c803, 0x762b7b90, 0x1296e98d,
                0xfe9eb1c7, 0x87e618b1, 0x683f2ba5, 0x55f16917, 0x5425b854,
                0x67c76438, 0xdfa7e079, 0x8c186383, 0xc7c335e4, 0xf367c66b,
                0x41a29e0c, 0x2d64635e, 0xa5f5731d, 0x9052717e, 0x71f935e5,
                0xfe16d869, 0xd9c2f2b2, 0xb2a0b033, 0x632723d8, 0xaddf4ccf,
                0x43584391, 0x90ebb95e, 0x370fe8c6, 0xef3efad0, 0x97724e0b,
                0x9c612503, 0xb31ed101, 0x85f96571, 0x4672abd1, 0xf93a9e47,
                0x4be4bacb, 0x107f67c0, 0xce195cf7, 0xf258601d, 0x06b4a612,
                0x29f5e2ae, 0xa4eb3e71, 0xe0365a09, 0xae4e63d7, 0x4922eeab,
                0x61334be2, 0x33c98022, 0x163f3805, 0x6b34c344, 0x70d2527a,
                0x9b81af66, 0xdedddae9, 0x011f3160, 0x4cfeacdd, 0x595d6eac,
                0x166e18d3, 0xb32711b2, 0x3ed0160b, 0xa17a9a77, 0x4555cd41,
                0xc00a6e83, 0xfedad44a, 0xea2ea1d6, 0x43e84ac1, 0x5e68d2be,
                0x33c86356, 0x45f52406, 0x6caab54a, 0x255c86d4, 0x7f2bd937,
                0xa34a8852, 0xb4a32e9a, 0xacf85da8, 0x6dcb5697, 0xf02d5653,
                0x6f4eb719, 0x1719e7ae, 0x3801b889, 0x6053f90e, 0x1cdcc375,
                0x4ddc25ff, 0x7d4671f1, 0xe8305eed, 0x6da58e90, 0x9dfa58b8,
                0x77247677,
            },
    },
    {
        .key = &kSigverifyRsaKeys[3].entry.key,
        .sig =
            {
                0x8402d200, 0x20710949, 0x14e1a980, 0xd8b157d4, 0x27b54e3e,
                0xbe67e757, 0x80f7c98a, 0xc1ddfd8b, 0x9b18b904, 0xc896742d,
                0x1fcee8ec, 0xdd9bfb3c, 0x73ade13d, 0x94eb5757, 0xb3220d27,
                0xae818424, 0xa0ff0c3a, 0x252ee390, 0x324925e0, 0xcbba4047,
                0xb7d32b18, 0xbc55e0e1, 0x0ba27a5e, 0x6a194fc0, 0x81553c9d,
                0x94a918cb, 0xd960f4d3, 0x54efa60a, 0x7c092981, 0x5ce781a3,
                0x458b9dad, 0x61666ba9, 0x9eda78dc, 0x71a80fd6, 0xa16f9727,
                0x20454195, 0x0ca82c15, 0xf48bc41f, 0x35448689, 0x9825d4ed,
                0xdfb4b7d5, 0xf0b5b7d3, 0x11ceedc4, 0x5279c565, 0xd59fd236,
                0x4fc04eb4, 0xa77edd38, 0x373fce45, 0xdc4719be, 0x7601a9f1,
                0x947a42ab, 0xac10049b, 0x98ab7ca6, 0xc2e2584f, 0x7e3097ec,
                0x826b27c7, 0x3d634ce2, 0x7e02edd3, 0x04cfa408, 0x4ab368fc,
                0xea5182d5, 0x15623948, 0xbd4e182f, 0x363dd200, 0xc38fe331,
                0xf3a9e7f8, 0xfad88dbe, 0xa2dfa44d, 0x4804773e, 0x257e556c,
                0x72cda358, 0x4f539e45, 0xb005b84d, 0x45d88360, 0xe142e88d,
                0x88ca7e99, 0x1a5738b2, 0x79fc2500, 0x9220496d, 0xc1ace896,
                0x0133c268, 0x9f3af45d, 0x9a82f6f7, 0x12541018, 0xf5315184,
                0xbef0cca0, 0x659c63f6, 0xb5707c58, 0xda2d7f72, 0x78a85a65,
                0x5121efc9, 0xfa335cd9, 0x30d87bf0, 0x50df50e7, 0x38cd6d9a,
                0x7a51b1bb,
            },

    },
    {
        .key = &kSigverifyRsaKeys[4].entry.key,
        .sig =
            {
                0x39b92a38, 0xf584ed48, 0x25f5f323, 0x04dde936, 0x608871c1,
                0xe234230a, 0x099f0ab6, 0xd31b9023, 0x65f0fd99, 0xa402880f,
                0xa0158ea9, 0xe7d34d13, 0x74f1edbd, 0x7a226c4c, 0xc77e08c0,
                0x1a863fda, 0xfd029480, 0x8470f80e, 0x2b03d2c5, 0x05ea5727,
                0x0ddb0df1, 0xa4096752, 0x6bee74d8, 0xa066d78a, 0x7f4d7423,
                0x2c8a6d1a, 0x0197361a, 0x1ac4e4f3, 0x3544b409, 0x993cac1a,
                0xf7fc8746, 0xb0037059, 0xdcb2155a, 0x7055a59e, 0x12e0c0be,
                0x5a9af17b, 0x4548dba0, 0x21822de6, 0x7a98b4d3, 0x4a0aeecf,
                0x35dc0641, 0xba5ac581, 0x0d0ba217, 0x6a15953e, 0x6b7d25b1,
                0x6e442c34, 0xdf522eb7, 0x0a0400d6, 0x66364428, 0x23e4938a,
                0x9edece9e, 0xe2f7fee8, 0x1701ac39, 0xe028f9fa, 0xdec374b6,
                0x89ca5e1e, 0x4bd8fa6b, 0x161850d7, 0x15601af9, 0xa41eeff5,
                0xe966cedf, 0x4889c9e3, 0x945fb580, 0xe5c1b9c2, 0x8630cbe2,
                0x62450f80, 0x46de9edd, 0xd0c1ac84, 0xa749097c, 0x8b3f0842,
                0xb3cb0b40, 0xc190341d, 0x42cc872a, 0x54825b43, 0x671b4f8a,
                0x7cc48f4e, 0x06e4f5ba, 0x0bde3406, 0xb6dee3b3, 0x0669fd54,
                0xd8d4c742, 0x31e67cde, 0x03fed7ab, 0xe1956b87, 0x28b7cc05,
                0x062f735e, 0xe3764364, 0x24f603a4, 0xb6399d4b, 0x14b9d609,
                0x9f49ce19, 0x8f14096c, 0xd3e33dab, 0x70b18505, 0x3b9a0fcc,
                0xc28540c8,
            },
    },
    {
        .key = &kSigverifyRsaKeys[5].entry.key,
        .sig =
            {
                0x1000e846, 0x07169294, 0x127738d6, 0x8a7d4591, 0x1534d609,
                0x828f8b3d, 0xba04c098, 0x2b5cb5f3, 0xc2f01bfe, 0xeb67c069,
                0xe629a7d4, 0xc3010bed, 0xc83c2976, 0x4284ec1d, 0x5d948638,
                0x2c19a493, 0x66a7b5e4, 0x0061a63b, 0x790b7653, 0x995344b0,
                0x51fb62ba, 0x271b691c, 0x1a029630, 0x732e22c4, 0x49bfcb29,
                0xb544d0e1, 0x5e850677, 0x2cda260e, 0x167c65e4, 0xe7f5a172,
                0x703ec329, 0x095528be, 0xeda599bb, 0x5ccb46f2, 0xbbac39d2,
                0x40f358e0, 0x94e8592f, 0x41ce65a0, 0x09580ffe, 0x80825ebe,
                0xc944a075, 0xa7de79a5, 0xa36f5d9f, 0xbb120eb8, 0x2e31a7b6,
                0xe6ed4cef, 0x49edfc2f, 0x9954867c, 0x5831aebc, 0x00df010f,
                0x9f950511, 0xfa13bf21, 0xd50c3bbe, 0x58c0b5c3, 0xe942bb50,
                0x06e2d763, 0xa0808d59, 0x40eab32a, 0x96e0ecb7, 0xa4c5712a,
                0xe0cf6d67, 0x730dfac4, 0x1cf5ecaa, 0x4230aa3e, 0xbb193d33,
                0x38b4685b, 0x62f208ff, 0x6b9f4ee5, 0xc0c58a59, 0x17b4b519,
                0x0bb58e9e, 0xbe99c087, 0x9e2d7649, 0x15f9d0ad, 0xbcba7ff5,
                0x4003b115, 0xf6a23bc9, 0x33ec053d, 0xfd8dcc01, 0x564b8169,
                0xb51aa972, 0x0d0cc0e2, 0xf372dbc1, 0x50ef195f, 0x6d8c221c,
                0x8588f6a1, 0xc56d5c4c, 0xea7396df, 0x7bb9bf11, 0xea147640,
                0x5a26751b, 0x1908434e, 0xa83b8e1b, 0x33cfa993, 0xdfc60f10,
                0x6d3b6394,
            },

    },
    {
        .key = &kSigverifyRsaKeys[6].entry.key,
        .sig =
            {
                0x59d916ff, 0x520a007e, 0xde5fa666, 0x9c212e52, 0xc1bc4784,
                0xd7c4e93e, 0x8128f84a, 0xf361f92c, 0xd6ef1c12, 0x6cd672d5,
                0x46f5555e, 0xc1e8d1e6, 0x7e6af491, 0x978e4a1a, 0xae9673c3,
                0xef0bc48f, 0xa0fefb7b, 0xa281deb3, 0x6b635b03, 0xdc35e3c0,
                0x02f8df52, 0x7e0eed5c, 0x91f43905, 0x1f2683ac, 0xfcd8993e,
                0x38dd36a7, 0x0cd5eded, 0x1de4d06a, 0x0463cee9, 0x19f032c7,
                0x66e06317, 0x67bfa617, 0x95171697, 0xc2c8af6e, 0x6eb98222,
                0x497f9941, 0xe5cf8175, 0xd6581df7, 0xc1f864c6, 0x1e22cf6c,
                0x427f7917, 0x6306448d, 0xcb5c20fb, 0x97abe71f, 0xbfc6c93a,
                0x25f1d638, 0x1f36ab56, 0xc89fa9bb, 0x038c2904, 0xe3029b6c,
                0x3596ac5d, 0x5d4ecff6, 0x2e4483d4, 0x9abe0721, 0x388f1831,
                0xa744f0b8, 0x2e44379a, 0x98b33358, 0xecaf5a9b, 0x999dd99f,
                0x88ff3789, 0x345f384d, 0x5ee3e13e, 0xced78d56, 0x9ad1d667,
                0x1353f133, 0xe349b83d, 0x5bf73b86, 0x2ae7f98c, 0x3374ca22,
                0xaf0cd370, 0xfc2e990e, 0x43d02247, 0xf9a97493, 0xcd390b45,
                0x6aeb242b, 0x0e0a7f5b, 0xe577a361, 0x82e21028, 0x8527e322,
                0x56b63190, 0x5df87caf, 0x9e69de56, 0xa0092de1, 0xd2d452de,
                0x3f9ebc02, 0xe4433770, 0xbc22c285, 0xa5963403, 0x7a7a6238,
                0x4d1625f8, 0x349588b6, 0x0534cd93, 0x0d8cc92f, 0xcfdcafff,
                0x0a9938f9,
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
