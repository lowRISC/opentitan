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

const RsaVerifyTestCase kRsaVerifyTestCases[1]{
    // message: "test"
    {
        .key = &kSigverifyRsaKeys[0].key,
        /*
         * echo -n "test" > test.txt
         *
         * hsmtool -t ot-earlgrey-z1-proda -u user rsa sign  -f plain-text \
         *     -l earlgrey_z1_proda_1 -o test.sig test.txt
         *
         * cat test.sig | xxd -p -c 4 | tac | sed 's|.*|0x&,|'
         */
        .sig =
            {
                0x4fb86cfd, 0xf7fdd873, 0x41d4e131, 0x42332f18, 0x2ab97596,
                0x92c93175, 0x6566f408, 0x075cf2b3, 0x97145052, 0x29e4ba4c,
                0x5152fcb7, 0x603dd114, 0xe48dafc1, 0x0418843b, 0xa112c41c,
                0x295beb6f, 0x69945bda, 0xbe6e2795, 0x5d7fc69c, 0x0be69a2e,
                0x046ecb6f, 0x8c87e16b, 0x1a25b186, 0xbc0f54e5, 0x8ff3c482,
                0x44cccdb8, 0x938de547, 0x69b1c859, 0xaac71a72, 0xb67a8f6a,
                0x80b83b4a, 0xd635ee33, 0x1e65ae47, 0xa729f2cb, 0x4c05badf,
                0x850a4c6c, 0xd9d11864, 0xa1722472, 0x4be3be2c, 0x341579ce,
                0x79e3d38d, 0xe837125e, 0x9beb0378, 0xd3ad2039, 0x6a2c1bb6,
                0xeb2cad92, 0xeaea8d55, 0xb0e46625, 0xe5ef2582, 0xbf6fdb2f,
                0x7eb49a77, 0xd7b95f10, 0x1fa7f93b, 0x889e32ab, 0xbc86289b,
                0x435c98dd, 0x6115e168, 0x28f1d1e3, 0x49ba7a8f, 0xd499d1b1,
                0x5c7939c3, 0x3dc3d71e, 0xf19d6bcd, 0xaa0181aa, 0x57abdee2,
                0xc1460f7a, 0x2b407075, 0x0d0f2b9c, 0x423ad869, 0xa36a20c3,
                0x27db5c2b, 0xef87d8ce, 0xab8076ea, 0x07633d67, 0x1648ddbf,
                0x93975efb, 0x210a8740, 0x9c02102f, 0x546ca508, 0xd886b7ca,
                0x3aff96bb, 0x77866a77, 0x16bee0d7, 0x2e468023, 0xc7f1bbf1,
                0xde2aa000, 0x2f97ee93, 0xcfdc6232, 0xadd317a2, 0xb40279db,
                0xd8e37a72, 0x3223ac4c, 0xd1f39f60, 0x83fcf17e, 0xdf1c7c6a,
                0xb8e10e6c,
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
