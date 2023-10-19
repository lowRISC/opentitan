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
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "otp_ctrl_regs.h"

namespace sigverify_keys_unittest {
namespace {
using ::testing::Return;

TEST(Keys, UniqueIds) {
  std::unordered_set<uint32_t> ids;
  for (size_t i = 0; i < kSigverifyRsaKeysCnt; ++i) {
    ids.insert(sigverify_rsa_key_id_get(&kSigverifyRsaKeys[i].key.n));
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
        .key = &kSigverifyRsaKeys[0].key,
        /*
         * echo -n "test" | openssl dgst -sha256 -keyform DER -sign \
         *     rom_ext_prod_key_0_rsa_3072_exp_f4.der -binary \
         *     | xxd -p -c 4 | tac | sed 's|.*|0x&,|'
         */
        .sig =
            {
                0x36eaced4, 0xfd86736f, 0x4be5bc52, 0xd58c0bad, 0x7bbaf753,
                0xe1d483d5, 0xb91e93df, 0xdc5a4d8b, 0x31a81dd8, 0x03964d74,
                0x4110c8e8, 0x4b26bd63, 0xeec9e880, 0x0658fbad, 0x9115acbb,
                0x30546e81, 0xd89b004a, 0x46ec0654, 0x7c790757, 0x40e5518a,
                0x5a8cac89, 0x77b9f7bf, 0xdde3ddb5, 0x74e3a826, 0xd63bfa53,
                0x72b514f8, 0xf6122729, 0x1196c0a4, 0x8c874559, 0xd7d8e6c9,
                0xa9dedeaa, 0xa7e09a18, 0xdcfd6da6, 0x31190e90, 0xf9e418ac,
                0xfdecd060, 0x422ffa89, 0x96b47e16, 0xfae6baab, 0x0e483c70,
                0x6ed98af7, 0xfdb5502a, 0xead118d2, 0x6fb8f362, 0xadfccb76,
                0x20c69cc4, 0x6a3eb2d1, 0x0ae30269, 0xf55a6c6a, 0xc7195f63,
                0x6178d106, 0x183df636, 0xc575b1c2, 0x0bfddb1b, 0xe3807c38,
                0x6fbe2b23, 0xf162c7dd, 0x47a54ad4, 0x45a48579, 0xa70aa643,
                0x77ecaa63, 0x77702f39, 0x5a7ded0c, 0x5c6db917, 0xfc5be756,
                0x119d6f7a, 0x4e55fe65, 0xbc3ad594, 0x753675d7, 0x909ad497,
                0x0bda2c0e, 0xc118e450, 0x99ac8b0c, 0xb1cd6836, 0x76dd6b92,
                0xd3e982b7, 0x8719abd7, 0xb1384cee, 0x86bbcbdc, 0xc211cab7,
                0x18ce7877, 0x9650d2ea, 0xda551fc0, 0x037bb2d5, 0x9dcadb98,
                0x8e65dd62, 0x582c6490, 0xc2f5e492, 0xc05f78f7, 0x24ee7700,
                0x682504ec, 0x46737d60, 0x482ab4a5, 0x23463420, 0x7b5b99c1,
                0x4293d6b4,
            },
    },
    {
        .key = &kSigverifyRsaKeys[1].key,
        /*
         * echo -n "test" | openssl dgst -sha256 -keyform DER -sign \
         *   rom_ext_test_key_0_rsa_3072_exp_f4.der -hex
         */
        .sig =
            {
                0x0a43b030, 0xa82d7c33, 0xb9b1228a, 0x5a0f8892, 0xaa58c077,
                0x365e2b25, 0xc5f013f8, 0xbf32bc11, 0x15350128, 0x07522924,
                0x8f7e0889, 0x82084b48, 0xb92b0077, 0x82d3514e, 0xbecda671,
                0x571009d2, 0xd4606ba7, 0x66bd5fc3, 0xddae3c76, 0xc388a4c3,
                0x808d5e2a, 0x2dc32965, 0x4e008e5b, 0x4abfc93d, 0xdb6eb16d,
                0x6cb028f0, 0x4aeffb6b, 0xe7574f3e, 0xff73b548, 0x08649d80,
                0xb2009425, 0xe2bbd368, 0xa28e3b8a, 0xdd2875cb, 0xc54fdf24,
                0x1a9a59ac, 0x54ee1013, 0x6da6244d, 0x5cfd3eaa, 0xc7cb551f,
                0x68626f79, 0xf1cd06c6, 0x5fe8eadd, 0x220c9362, 0x8cc33f50,
                0xc3918984, 0xe1967286, 0xfd0376ac, 0x41e0f3ee, 0x5f221d07,
                0x90803f71, 0x6c7cef85, 0x835975e7, 0xa6b9fee5, 0x87155038,
                0x0fb5407e, 0x050f0cd0, 0x85225aec, 0x0a407a9f, 0x5a175126,
                0xe2e67818, 0x21deaa56, 0x9df45426, 0x361f14ab, 0xd93d22e7,
                0xb9cc475e, 0xe8b28289, 0xc56fbc95, 0x18b2d1ab, 0x14e18896,
                0x07ff5105, 0xce8f5e9f, 0xdee539a9, 0x2cf56ccd, 0xabe93abf,
                0xc51bee68, 0xd29df209, 0xebba0ab8, 0x9985a37b, 0xf30ec0fb,
                0xeba0bf7b, 0xa508045c, 0x02f09bb2, 0x9f674fe3, 0xb9c07238,
                0xc9c88282, 0xada38689, 0x6d7c3294, 0x479e27dd, 0x01bd6436,
                0x412c377f, 0x51a56959, 0x530432e8, 0x53e4f546, 0x163d3282,
                0xc25256a9,
            },
    },

    {
        .key = &kSigverifyRsaKeys[2].key,
        /*
         * echo -n "test" | openssl dgst -sha256 -keyform DER -sign \
         *   rom_ext_dev_key_0_rsa_3072_exp_f4.der -hex
         */
        .sig =
            {
                0x6e317a1c, 0x9068313e, 0x3f9610c1, 0x261cb66b, 0x0d6f49c6,
                0x6e062654, 0x87a0febe, 0xae824f16, 0xeca90143, 0x56ea924c,
                0x34dc1f64, 0xa9b756f9, 0xa6965f0d, 0x366c89cc, 0x921520ca,
                0xab0c17ec, 0x199a0b02, 0x6551663a, 0x9ff7ab3e, 0x4aea7455,
                0x3a3d6b2f, 0x0e8fe77e, 0x1b18ed7c, 0x643168d0, 0x91de7e47,
                0x86190fc2, 0x7b9b7a64, 0x5784b535, 0xb358354a, 0xad42ed4c,
                0x539823a8, 0xe7cf98ec, 0x68c4a7ae, 0xad35612e, 0xc43c18c6,
                0x5da4fa0b, 0x918a15b2, 0xbde51df7, 0x5d63a9d2, 0x96af2137,
                0x02c1cf63, 0x0a285e1a, 0x4d228a24, 0x45aa181e, 0xdefe4371,
                0x5a6c986e, 0x1d5455a5, 0xf342a7f2, 0x9e6d116f, 0x0cde267b,
                0x360997c0, 0x5da55860, 0xfe2ccf61, 0xc9517096, 0xb5e3891b,
                0xa7a0194b, 0xa1b094bd, 0x1dd61621, 0x79061426, 0x5eba1c71,
                0x5e3981c4, 0xcd38b155, 0xe47d6d5a, 0x985ef71c, 0xe69e4ba9,
                0xbfec165d, 0x1f5beff6, 0x15f18950, 0x18173348, 0xdfb7d0b2,
                0x8379cf38, 0x16636f15, 0x8b741f64, 0xd7bbd6e6, 0x0915d0fa,
                0x16f60d28, 0x54966caf, 0x5d415bc1, 0x2f033158, 0x140efe45,
                0xe0ed8089, 0xa79d27fa, 0xb256bf12, 0x4597dc61, 0x75d62c3e,
                0x18cb1285, 0xdedc32a3, 0x7238f240, 0xe9c7e35b, 0xecab323e,
                0xf39e74b9, 0x04cba244, 0x36ff5c6a, 0x5ed63996, 0xe5510a91,
                0x536875ef,
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
