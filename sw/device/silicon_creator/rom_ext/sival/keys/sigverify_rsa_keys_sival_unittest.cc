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

const RsaVerifyTestCase kRsaVerifyTestCases[1]{
    // message: "test"
    {
        .key = &kSigverifyRsaKeys[0].key,
        /*
         * echo -n "test" > test.txt
         * hsmtool -t ot-earlgrey-z0-sival -u user rsa sign  -f plain-text -l
         * earlgrey_z0_sival_1 \ -o test.sig test.txt cat test.sig | xxd -p -c 4
         * | tac | sed 's|.*|0x&,|'
         */
        .sig =
            {
                0x51f8a313, 0xdf9cadc8, 0x09849651, 0x3396dc50, 0x2523715f,
                0x3f261117, 0xbc891dc0, 0x25e90a18, 0x7f3d68ef, 0xa49e89a9,
                0x1e126205, 0x566de5eb, 0x1302edc8, 0x85a11622, 0xedf3b295,
                0xbf2ead9d, 0xe2f7f62e, 0x82014f37, 0x62114a4f, 0x64d71f3d,
                0xef9f97ae, 0x222a67e2, 0x47fd6d82, 0x8fd3f870, 0xdf07454b,
                0x1a627fc1, 0x5697e480, 0xb5b4857d, 0x865bd8ce, 0x1f7fdc3a,
                0x436807eb, 0xf0954b96, 0xd7556c4e, 0x6056c8d4, 0xc5e7875c,
                0xdc4d5cdc, 0xba128354, 0xb57fccef, 0x367d4b88, 0x2b54c85e,
                0x711b9cab, 0x747b8c65, 0xe98fb5d1, 0x272c0705, 0x9db1bf83,
                0x33e18070, 0x7b4f73b1, 0x584e0de9, 0x75e103c2, 0x68062c61,
                0x910b2c9c, 0x2af9ff03, 0x114d2bef, 0x278c2036, 0x1e63481e,
                0x8fefabfd, 0xdac1fbaa, 0x769d708c, 0x94f5c336, 0xa07835b3,
                0x0f1ee10e, 0xfe905d90, 0x5b561fe7, 0x686dd4a6, 0xb6e3507f,
                0xadba5635, 0x9e463d0e, 0xa782afaf, 0x43366fa1, 0x7146b3c4,
                0x9f4d2baf, 0xd9aed324, 0x36f0a5a2, 0xfa041f9d, 0x32f2fb3a,
                0x6b56b1df, 0x2fbfceae, 0x3fe7dbe3, 0x8458b9db, 0x29860b30,
                0x40bc9b9b, 0x36515839, 0xb414bfab, 0x6df1cfd2, 0x50431bef,
                0x3fb2c08b, 0x7b733a06, 0x534c39f1, 0x5cd5f48b, 0xcc488cae,
                0xb08b1fca, 0x62f9c45a, 0x72e3e064, 0x34f7fb4e, 0x64a20ebd,
                0x0c7d4fb0,
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
