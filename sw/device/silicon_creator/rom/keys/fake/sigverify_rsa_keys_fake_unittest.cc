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
    /* message: "test"
     * The arrays can be generated with the following command:
     * echo -n "test" | openssl dgst -sha256 -keyform DER -sign <basename>.der
     * -binary | \
     * xxd -p -c 4 | tac | \
     * awk 'BEGIN { ACC=""; cnt=0; } { ACC = ACC " 0x" $0 ","; cnt += 1;
     * if(cnt==5) { print(ACC); ACC=""; cnt=0;} } END { print(ACC); }'
     */
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
                0xfec060dc, 0x75bdfe70, 0x27c0e2f4, 0xaed484a2, 0x3313bc18,
                0xf418d734, 0x155aa6d4, 0xf9f484cf, 0xea37a8a0, 0x4003c321,
                0x81e819de, 0x1e938394, 0x695d8516, 0xb1b5c19f, 0x2bdebb3e,
                0xcff52612, 0x84a3399b, 0xa9555cb8, 0xb290375a, 0xe68fea40,
                0x90968ec8, 0x8c804bce, 0xe76981bf, 0xa2fbb612, 0x54055d03,
                0x260834ef, 0x5021b7dc, 0x90f45057, 0x716b2fba, 0x224b5519,
                0xcae52a50, 0x0edc2cc9, 0x77f65f96, 0x95aa3f6d, 0x66335de3,
                0x6bd90f1f, 0x16a68d27, 0xccfceb7a, 0xeffe80ab, 0x788ed06c,
                0xa48506b1, 0x2a53f589, 0x2c0d7e26, 0xcef7f81b, 0xb7495fbd,
                0x5bb06b51, 0x97bd2f6d, 0x8ce61ba5, 0x3c23db97, 0x637e5d18,
                0x494d570d, 0xc5ae8923, 0xe0ec7255, 0xdd523900, 0x20a691f8,
                0xea9faba8, 0x0d017632, 0x2ad5fe98, 0x323e01d8, 0xf5fd36ac,
                0x2ff408db, 0x021f67d1, 0x04aac7ac, 0xe327f479, 0xc0bb5610,
                0xd4c6836f, 0xbf64f264, 0xc805e2e2, 0x2c2c35d1, 0xead8b7b6,
                0x923db247, 0x6f5cd2e4, 0x15243500, 0x69d6206b, 0x4a8dab7f,
                0x64027644, 0x2e6b7c97, 0x7ea511f3, 0x59a1b71d, 0x5a26901e,
                0x1cb6460d, 0xec87eb1b, 0x96cad13f, 0x5238b070, 0x846bfc5a,
                0xa73b908a, 0x23469606, 0x7b5b738d, 0xe8332815, 0xda797d7d,
                0x15a4ceb6, 0x978c78c0, 0x583e5503, 0xc32232f6, 0x4f4eff49,
                0x7aed55ac,
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
                0xb5145f51, 0x785066f5, 0x6a08b856, 0xbe98880a, 0x4c842616,
                0xa3a2e744, 0x2c198ec0, 0x045d3230, 0x257c4d32, 0xb36ccac4,
                0xacf21959, 0x9b68d7e9, 0xb3189ae0, 0x533b517e, 0xc6330a06,
                0xd446a551, 0x1668fbaf, 0x8a14d5ba, 0x252db9dd, 0x38542681,
                0xb2ba9909, 0xb3c14c82, 0xde4d0bc9, 0x9ee0899b, 0x68ff7a4a,
                0x04344bcd, 0xb706ad94, 0x499ed281, 0x1fa4a0b0, 0x31fd70f0,
                0xd0dcb77c, 0x27b0645d, 0x15651c0d, 0xab949acd, 0x90a20a6e,
                0x3bc3df50, 0x9b4c249b, 0x4eaafd17, 0xc90da438, 0x0f14d16d,
                0x1fa9132f, 0x4876817b, 0xe2636cb6, 0x2cba25d3, 0xcc3ab9bf,
                0xb056653e, 0x2fc2352b, 0x20fe4e44, 0x03c63d30, 0x700c82fd,
                0xf68efb0b, 0x90a07789, 0x81426314, 0x25852991, 0x3a1c11a9,
                0xb4ea6ec7, 0x646215cf, 0xc2eac6b8, 0x0e7e6e82, 0xf0e4d324,
                0x8b665521, 0x42dd65e8, 0xa260d000, 0xad36b184, 0xdebcb874,
                0x5d70f17c, 0x626f91e2, 0x3aec60dd, 0x4415c8a7, 0xd0b1b083,
                0xb66777ab, 0x8971648f, 0x439cff5f, 0x787be1bb, 0x2944a546,
                0x1f9ede0f, 0x6863df5c, 0xbca97608, 0xa2a017d2, 0x9bf92ada,
                0x83256b95, 0x133cac5c, 0x25ec3edf, 0xa5d5a84e, 0x322fb6bd,
                0x53ea3b1f, 0x8ce9a3eb, 0x55461726, 0xa3007b7f, 0x42a21f74,
                0x663811da, 0xbfd31571, 0x3ec4e4c3, 0xcd82a25a, 0x601ad6b4,
                0x43a3a803,
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
                0x6ee438bd, 0x5e6b1f54, 0x9ca3ec7f, 0xf2bdb245, 0x017527d6,
                0x364392e7, 0x3a7aefe9, 0x363178f5, 0x4541fcc1, 0x53584df8,
                0x8850e459, 0x69be6e1e, 0x60b474cc, 0x6277b197, 0xd2753c90,
                0x3176d9a5, 0x0d7049ce, 0x782170cf, 0x4f74dbd9, 0x2703a948,
                0x656ec2a1, 0xb8b78205, 0x18d104f0, 0x21a6c307, 0x1f5c054c,
                0xb13370b4, 0x989889f8, 0x10424256, 0x3e90d0e3, 0x18e4136c,
                0x249d4bb5, 0x57b1ba0d, 0x2c09a14e, 0x6e945879, 0x6c57e075,
                0xd04d0b78, 0xa3a0f966, 0x0985c344, 0xd913caf9, 0xeb79c157,
                0xf1693341, 0x89c133fc, 0x91d417bc, 0x7a749b82, 0x3dd5405a,
                0x156473bc, 0x9962d54a, 0xa00cfbee, 0xa08d40aa, 0xdb56829f,
                0x4e91fc26, 0x11afe123, 0x17c13601, 0xed45e192, 0x913b8d3b,
                0x18f3f1ae, 0x93068723, 0xc2189bb2, 0x0254d52a, 0x2f039e35,
                0x170b58ad, 0x93f4e4c5, 0x1371794d, 0x83cef155, 0x45acc14f,
                0x06cf773f, 0x499cd5e6, 0x110c59ff, 0x1d187e41, 0x20c3365a,
                0x0cb390ca, 0x8370cc52, 0x74a9c0ac, 0x5bec7027, 0xabc40f2f,
                0xdf0c41ff, 0xc32e9938, 0xd613fa2f, 0x6e789c8c, 0x0f0afdac,
                0x23cab2cf, 0x81822dda, 0x565bf239, 0xadb04634, 0x2b28211a,
                0xee2fab60, 0xcb8a5a09, 0x654a43e8, 0x44f2977f, 0x325c3166,
                0x1c2b937a, 0x55985d54, 0x2bd3dcdb, 0x1a958986, 0x8fda8da8,
                0x30fb1482,
            },
    },
    {
        .key = &kSigverifyRsaKeys[6].entry.key,
        .sig =
            {
                0x82bbf83c, 0x992387cc, 0x5676370d, 0xb6ba7e64, 0x28856d78,
                0x79aa55a3, 0xfa450d08, 0x28da8b48, 0x3237ed67, 0x01b3c445,
                0xa0efd443, 0xf157e13a, 0x151b4d68, 0x5bd329c0, 0xb9676c85,
                0x70bdfd54, 0xd8fb4670, 0x6fc14115, 0x1cbfda8e, 0x0f114585,
                0x2ff0d4bd, 0xfef11082, 0x3dbe96ac, 0xc21e58a0, 0x135b5b54,
                0xfdb2bd99, 0xbb01ecda, 0x547e4fe8, 0xff200caa, 0x065463a8,
                0x3946495d, 0x280dec9a, 0xfaa35220, 0x3d257253, 0x247c87dd,
                0x0b3d9bc4, 0x645e78dd, 0x24a22322, 0x0797f199, 0x695c2e12,
                0x3baa018c, 0xfd4944a3, 0x07809d1c, 0x2d64ceee, 0x460e774b,
                0xf161a4a5, 0xf49f7aef, 0xdd2f0e5f, 0x30da5954, 0x3bf5a294,
                0x84f235fd, 0x51970b52, 0x720af0a7, 0xde450de6, 0x00044020,
                0xca715caa, 0x7abf9b7d, 0xcff255b7, 0xf99a46a6, 0x56fbd9b1,
                0x066572b3, 0xbe474d46, 0xe08f5075, 0x5b5e5bbd, 0xc61d382b,
                0x952dfecf, 0xf8337e0d, 0x7c151be9, 0x9b6e55dd, 0xb2fb444a,
                0xbfeaeeb3, 0xc10884f4, 0x2d9ede92, 0x29261a15, 0x99d6f539,
                0xb2b72814, 0x4357e038, 0x760fa698, 0x60caa628, 0x3df34a31,
                0x48d350d7, 0x11ae8413, 0x1ee614f9, 0x94d5e183, 0xe41ddf8c,
                0x79b99e46, 0x3b87b2ba, 0xf7714ba3, 0x78d3f683, 0x2745545c,
                0xd16e6265, 0xed2b8416, 0x4607b7f7, 0x3e0d7045, 0x6900d704,
                0x64887835,
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
