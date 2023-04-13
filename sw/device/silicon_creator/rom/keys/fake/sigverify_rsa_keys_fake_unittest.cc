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

const RsaVerifyTestCase kRsaVerifyTestCases[3]{
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
        .key = &kSigverifyRsaKeys[2].entry.key,
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
