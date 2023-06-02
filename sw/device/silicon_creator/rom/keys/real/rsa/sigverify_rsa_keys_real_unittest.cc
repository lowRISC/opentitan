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

const RsaVerifyTestCase kRsaVerifyTestCases[]{
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
                0xcffc7b85, 0xc7c9473e, 0xce8164d9, 0xb8e38bd2, 0xe9b0a770,
                0x8934cb0b, 0x9519c4b5, 0xc7994e18, 0xab646130, 0xe7b473dc,
                0x2f31aaa0, 0xf9cc1ba2, 0xa9e42be3, 0x54659e70, 0x3af920a3,
                0x5de88438, 0x4874c85b, 0xf4fe99e7, 0x8d7257e1, 0xabdaffc2,
                0x00069aa0, 0xab9ea1fc, 0x5caa00ae, 0x6d713e5e, 0x26254218,
                0x446dc2c1, 0x0971349e, 0xf65cfe2d, 0x5906e936, 0x742f4fa9,
                0x88487b3e, 0x7864f3e2, 0xa74879f7, 0xdbeb175d, 0x005f2945,
                0xdf90ff7b, 0xa742644f, 0x10f5ba21, 0x509d5104, 0xeee45f8b,
                0x457b1c4a, 0x67312d74, 0xeb71af86, 0x66415e79, 0x8edc5a9d,
                0x534a1413, 0x2da95ef2, 0x117c4f69, 0x04da244e, 0x758b2c3f,
                0x80898d4c, 0x73bc5802, 0x1f1a0f47, 0xba3cc60b, 0xe6731f48,
                0xa67ad69a, 0xcfaf029d, 0xc3f0502d, 0x2c4c8184, 0xa59c161e,
                0xf0dc3372, 0x3098299b, 0xe4556755, 0x27166216, 0x811ff225,
                0x60c12727, 0x7056d26b, 0xb0570fd6, 0x9468663c, 0xa75af35b,
                0x4f50d5ed, 0xc96906e0, 0x7a16b79d, 0xf8b8d88a, 0xf85b213e,
                0x3a358e69, 0x94d50d38, 0x713e62ce, 0x7d50712d, 0x92826f29,
                0x30c62dac, 0x1d820cda, 0x4b5b8165, 0xa872156d, 0x8a6b96d1,
                0x7e7f7ff5, 0x98454a1a, 0x3506c94b, 0x5498614d, 0x404422dd,
                0x6f13b7f7, 0xbe5963b8, 0x39848552, 0x6f2793a8, 0x7fc07e63,
                0x909a35d0,
            },
    },
    {
        .key = &kSigverifyRsaKeys[1].entry.key,
        .sig =
            {
                0x73e2d707, 0xbb348f48, 0x73364489, 0x81d64150, 0x3e871eec,
                0x28ffb411, 0xf795c93b, 0x6f44e0ad, 0xfbcc7ab7, 0x99fdff1f,
                0x824d702c, 0xf7106620, 0x4e988d36, 0xac81f3a3, 0x61b34c9d,
                0x5c59fb22, 0x53b3173c, 0xbd265248, 0xd4a0b0e0, 0x38c1038b,
                0xec7279d9, 0xb2877cd0, 0x8ef48cf4, 0x6f0e6e5a, 0x2da021f4,
                0x0b1940cd, 0x902caf99, 0xe3e447e9, 0x65a62b21, 0xc7ff8880,
                0x94892803, 0x3cd77727, 0x98206f26, 0x2861a975, 0x0cd08a98,
                0xae930ebc, 0x546d6bf3, 0x255a1c8a, 0x0e1a4d60, 0x4c3e6e23,
                0x7029fe02, 0x7b444b14, 0xdb92d858, 0xef03d6db, 0x278073f3,
                0xd9fd58ef, 0x00cf1e4b, 0x9d00f5a5, 0x1c3c3eb1, 0xe345a05d,
                0x4057f315, 0xb59c0fb4, 0x00b07f63, 0xe33d6a72, 0x1a69c25c,
                0xaad99f37, 0x3cae82c2, 0xad5f46ea, 0x54c64815, 0xfeaaec36,
                0xc8396676, 0x2fbfec49, 0x79cda569, 0xb652b999, 0x9abc2d56,
                0x5b3f6a1b, 0xb2e9cb40, 0x480b2bf8, 0xdcaf9089, 0x228386d5,
                0x3aee67c3, 0xdddc4bf6, 0x89eb60b7, 0x6cd85df1, 0x7ba96fe8,
                0x7e32afa3, 0x23464114, 0x7692aeed, 0x1537853f, 0x8502a51d,
                0x39aec363, 0x6eed77d5, 0x98984bef, 0xe4b50087, 0x74d1e010,
                0x5305949a, 0x1cbcb5ca, 0x960f38f5, 0x98f01248, 0x4f490028,
                0xd170d33d, 0xece24d7a, 0xe777427d, 0xae52c5cc, 0x69fc601e,
                0x334354ed,
            },
    },
    {
        .key = &kSigverifyRsaKeys[2].entry.key,
        .sig =
            {
                0x5daf0025, 0x8ed5af6c, 0xa15406b7, 0x189a123b, 0x2b219a56,
                0xe570c588, 0x16c3eced, 0x36a67298, 0x1d9f55ba, 0x80a685c4,
                0x30d3d015, 0xd4ae4250, 0x02defad6, 0x3529e813, 0x3a81cebe,
                0xfd14dbfc, 0x27ac9a0f, 0xa9c137dd, 0x85e0046b, 0xcdc8535d,
                0x44dddcc9, 0x77cc6381, 0x04ee2d4e, 0x1dec4e82, 0x85b61ea6,
                0x9e3d9188, 0x50080cad, 0x9bda35d2, 0xc032e7f5, 0xcec2f96f,
                0x764a55bf, 0xf6369129, 0x8927b376, 0xfe78e65a, 0x7068cd3a,
                0xa93d56ab, 0x190a66f1, 0xf623e126, 0xd980cfa6, 0xff8f9004,
                0x42cad49b, 0xf706b2ef, 0xbd9ca477, 0xd822f164, 0xd4680c64,
                0x677c3763, 0xe6cad677, 0x8f53fa3a, 0xfe3402af, 0xe77a0d95,
                0x179fdeab, 0x3a87192b, 0x34c44684, 0x3e601d1e, 0x972301fc,
                0xfba46b52, 0x03890239, 0x25879672, 0x5538f181, 0xa2e105af,
                0x7a52a4ef, 0x729d33ff, 0xede3715f, 0x87e9713a, 0x8b17402f,
                0x167c1e31, 0xd1dd36c1, 0xe19216dd, 0x260fd526, 0x8bdb861c,
                0x7dc54321, 0xaf281c8a, 0x25457936, 0x89edb182, 0x70017a2c,
                0xf650d206, 0x10869030, 0x2c15acf6, 0xab977be4, 0x637aff53,
                0xb32a6ed0, 0xf1f000f4, 0x1497877a, 0xec159d29, 0x515a9ffb,
                0xcae481bd, 0xf1d9c087, 0x1dbb391a, 0x5d142025, 0x853c29de,
                0x4728758e, 0x59816611, 0x229546cc, 0x1602c682, 0xb39f0e12,
                0x046c5ca3,
            },
    },
    {
        .key = &kSigverifyRsaKeys[3].entry.key,
        .sig =
            {
                0xaecea6c8, 0x7ccde7c3, 0xfdd2b4d9, 0x43db4b80, 0x415a4ec9,
                0xf34d2955, 0xf2fe5758, 0xbbbb6a68, 0x1404f7e6, 0xd4f822d5,
                0x242a2327, 0xc3034991, 0x667094be, 0xed2025e3, 0x51dc6792,
                0x5bec1b69, 0x3d5d7a43, 0x35f94b93, 0xc5e5fc9f, 0xacd2aa4a,
                0xbfd03e65, 0xe666a9aa, 0x684c3129, 0xc7e0948e, 0x5dc200e4,
                0x171f21fe, 0x7e5b3f89, 0x10ee9467, 0xb06f22da, 0x739dc1c1,
                0x80f9f118, 0xa64e9068, 0x5e8cb24d, 0xf3617b1b, 0x531f106b,
                0xa0168457, 0x4c0697eb, 0x92623ac9, 0x1693adb2, 0x5bb87413,
                0x6295c6c2, 0xdbf29d63, 0x936a8d6c, 0x60f89edf, 0x5f610682,
                0x60db9fe7, 0x09f0a4f0, 0xdd89e5c9, 0x9d626461, 0xfc62e866,
                0x36812711, 0xce4ed682, 0x1c24c2a4, 0x23e4a5a7, 0x7d9f2624,
                0x1f78ac1b, 0x96575dae, 0xccb741be, 0xdd1b675a, 0xc1ddf094,
                0x4a3e10e2, 0xedfb74a0, 0x11f4054c, 0x2906839f, 0x8a875916,
                0x559eebde, 0x923449c3, 0x99b4b096, 0x560ff613, 0x3081ecdc,
                0x6af541df, 0x8db82086, 0x31f5bee6, 0xd4b5e6b2, 0x62ae28d0,
                0x5eaff146, 0x0d56ce81, 0x64b1f500, 0xd9b47a7e, 0x7fa832b9,
                0x46fc6854, 0xc2a5cd26, 0x38cef3c1, 0xc87ea457, 0x86ad57ad,
                0xe1c65809, 0x136a0961, 0x365fa51d, 0x64666871, 0x77cc78f8,
                0x87eac8b1, 0x86456496, 0x229a043d, 0x251e834d, 0x8ba3a732,
                0x3a52a4a4,
            },
    },
    {
        .key = &kSigverifyRsaKeys[4].entry.key,
        .sig =
            {
                0x23cf159b, 0xc49dafcc, 0xd5ee3e18, 0x84ee8cf3, 0x6d0a4736,
                0x1b1ea72e, 0xc4c58293, 0x16414f57, 0x749cd743, 0x28ca7a69,
                0x445b3a54, 0xa8892fa6, 0xa64b76dd, 0x9d6c057c, 0xeaf1b1d0,
                0x6f845186, 0xd15c1092, 0x4f58a5cc, 0x9b37e505, 0x5ab34575,
                0x21266ec7, 0x42ff4091, 0xfbffd704, 0xa4687c5b, 0xba7468ae,
                0x293587d9, 0x12947f88, 0x37e3a7d2, 0x3992461a, 0x48680170,
                0x3ff3a190, 0x66428e9d, 0xf6bd7a02, 0x1179b50c, 0x7935990b,
                0xed4a8547, 0xe837ddce, 0x62001c65, 0x266778e6, 0xd112c1e9,
                0x6ae1be31, 0xe2af8808, 0x9ee6ba42, 0x8379150a, 0xda78e10e,
                0xa0d4e35b, 0xc2b05954, 0x4ec120a6, 0x279136bb, 0x81cd47c1,
                0x5dffe528, 0xed91ee5c, 0x40ca48e5, 0xe8270928, 0x4b437efb,
                0x11b21ed5, 0xe26f811a, 0xf1916a15, 0x4962f440, 0x8bc09baa,
                0xf6f12296, 0x100325e0, 0x67e5acd2, 0xab4a15d5, 0x89cd18ca,
                0xb8bd4fc8, 0xc67adef0, 0x6bf9063d, 0x37d9fe9c, 0x72129a86,
                0x6d2c5747, 0xde97574a, 0x62629f05, 0x7974a1e0, 0x9068a2e0,
                0xe68edb63, 0xe481f4f3, 0xe0f54678, 0x4ff9630c, 0x1f0be24d,
                0x6ac089d2, 0x948413c2, 0x6673bdf6, 0x9b54c64e, 0x7e94c9c8,
                0x85b8766d, 0xa7a3311f, 0x8709f5dc, 0xf44c4bcd, 0xaceb8249,
                0x825680da, 0x9324ddf4, 0x2279f0c0, 0x9414f511, 0x089cedc2,
                0x346f54fc,
            },
    },
    {
        .key = &kSigverifyRsaKeys[5].entry.key,
        .sig =
            {
                0x7eb5a94d, 0x9f4e5cbe, 0x2409b947, 0xdb753079, 0x2d5ed62a,
                0xa999e637, 0xdb51ff13, 0x61e7545d, 0x09233b4c, 0x1e97956a,
                0x4a5dfb60, 0xe1409135, 0xde4d5d0f, 0x116bd374, 0x067fc978,
                0xa7d07e03, 0xb0f0e5a3, 0xa0d67962, 0x0585a5cd, 0xd8253de6,
                0xed9bc2be, 0x21399a78, 0xcb206a1d, 0x31c305dd, 0xb680eb1f,
                0x4a73f9b7, 0x042c899a, 0xe9bf615d, 0x904a7572, 0xff61d44c,
                0x01446693, 0x03ea0119, 0xe639e481, 0x7b4ef8f2, 0x08262389,
                0xd228273d, 0xe8ccd706, 0x16b30d90, 0x8ae85d50, 0xf5bd1b41,
                0x64781443, 0x316b2a71, 0x2f801fae, 0x6ac20f9d, 0x0408fdb1,
                0x61871d8a, 0xac205660, 0xfe33f7e2, 0x22a25cc4, 0x3e1e242b,
                0x4c81534c, 0xe50a2749, 0xb91a77d9, 0x16be6cd2, 0x990ac5bf,
                0xfc96e741, 0xdf3676e6, 0x1c8568c5, 0xa7877663, 0x6fc9b714,
                0x35b04c73, 0x38f1eb40, 0xe0f6c17d, 0x80bf3909, 0xa726156f,
                0x28f8c28a, 0x2a62891f, 0x9d5e8ac7, 0x126d33c4, 0xb64e8890,
                0x769cba53, 0x9fee519d, 0x5d35ceba, 0x22f7e627, 0xe7932c93,
                0x7e5afe9f, 0xc37954a8, 0xc39c9284, 0xf8d29a12, 0x895f3cf5,
                0xb6f2c30f, 0x3a4298df, 0x183b5504, 0x038afda2, 0x551703a2,
                0x1dd9a69f, 0x86f2477c, 0xe7f896e6, 0xdd7876bd, 0x6b3d11c0,
                0xa81afaaf, 0x42179999, 0x654a7141, 0x63a1a367, 0x6b9dacc9,
                0x49ee838b,
            },
    },
    {
        .key = &kSigverifyRsaKeys[6].entry.key,
        .sig =
            {
                0xf4b70209, 0x3991743a, 0xcf8ae652, 0x444e0fb0, 0xcdd48c5e,
                0xfe311c60, 0xdccd66bc, 0x9aa7907a, 0x05d2294e, 0x15689a38,
                0x067c57e4, 0x8754ddc7, 0xb1674437, 0xfba4fff4, 0x1800b2e7,
                0xcbb21401, 0x58f8d6a6, 0xf79554eb, 0xb6ad50f0, 0x5d7f4e22,
                0x5392e2ed, 0x394bf0af, 0x0317f99f, 0x185b65e3, 0x830e1202,
                0x9526bf50, 0xb120a70f, 0xa230871e, 0x9a5fa89f, 0x6b5e50e7,
                0xb3b57198, 0x022e6bca, 0x094b1aef, 0xecefeda6, 0x4304eeee,
                0x53952508, 0xdb83075c, 0x58ab4bdd, 0xe2721ab1, 0xdbb9f83c,
                0xc5d8cfb9, 0x0550a25c, 0x46bd4efc, 0x6b8ccd5c, 0xde00b966,
                0x97f1c775, 0x935c7f96, 0xc91baf93, 0x3b057f69, 0xe34086c1,
                0x778a50b4, 0x5c82dd79, 0x0b40bab2, 0xe2037eea, 0x6faccba6,
                0xf349c201, 0xaa74ecec, 0x7c77adab, 0x1addb3b4, 0x9ca550a8,
                0x761e1be5, 0x1e32f2e3, 0x3ec2ce92, 0x683a7919, 0x5a80a087,
                0x4f4b7e57, 0xcc0875ef, 0xc105fad4, 0x28f42a95, 0x28d1c195,
                0xe7df7628, 0x850fbd44, 0x7102d47f, 0x6ceabe64, 0x948d6f15,
                0x7a4ef0c6, 0xf126f6fd, 0x07662fbc, 0x4fa1d61c, 0xdcc1f100,
                0x471e94d8, 0x7ccec6ff, 0xa284970c, 0xa4b47fb0, 0x9ff9c33c,
                0x68f0070a, 0x18c69824, 0xcfe0be79, 0x88f762f1, 0xa3d5f136,
                0x921ec30d, 0xfb3428d6, 0x1824b9e6, 0x48f55ee9, 0x73bed53d,
                0x8f5c0b78,
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
