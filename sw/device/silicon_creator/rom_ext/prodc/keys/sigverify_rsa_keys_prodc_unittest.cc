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
         * hsmtool -t ot-earlgrey-z0-sival -u user rsa sign  -f plain-text \
         *     -l earlgrey_z0_sival_1 -o test.sig test.txt
         *
         * cat test.sig | xxd -p -c 4 | tac | sed 's|.*|0x&,|'
         */
        .sig =
            {
                0x8f377053, 0x84f3b28b, 0x679a0612, 0x0c6113ce, 0x866d2e26,
                0xc77cf46f, 0x6b4fbc29, 0x6ee46599, 0x5f4fb71e, 0x2545331c,
                0xf348d902, 0xcb99fd20, 0x0d847abc, 0x9beead72, 0x1c2120bf,
                0xfdd126f7, 0x360857af, 0xccaeb60e, 0x071bc97b, 0xa1153749,
                0x13a70f63, 0x78f7656a, 0x87335c35, 0x17cf900c, 0x178f4da0,
                0x92bdd3cf, 0x2e2b07ff, 0x2c9966d6, 0x62f3f6fd, 0x0d798700,
                0xfe7f6dfd, 0x4fff2fcd, 0xd3659016, 0xd6b2294f, 0x9a9b435b,
                0x88bf97ea, 0x15216b1d, 0x0a5c8a57, 0xae01e283, 0xf3a5f516,
                0x08d85472, 0x0fc112db, 0x9f8b9176, 0xf5b934ed, 0x2477c59d,
                0xb08e660b, 0x0cac1047, 0x9dcb7e15, 0x95172f46, 0x54534029,
                0x521e1305, 0x1287fa18, 0xc612a532, 0x0c9c6adf, 0x13af326e,
                0x0c821490, 0x34f1df90, 0x6e06b13a, 0xecd46938, 0xf8677789,
                0xfeb279e9, 0x10e7af0e, 0xdf822495, 0x3643f357, 0xf663ed24,
                0xb3d178a5, 0x668c2172, 0x3c6348cb, 0xec3f2790, 0xd5daf3c9,
                0xab9fa6ee, 0x8c43b22e, 0x9dd8d59b, 0x02d762ec, 0xbd671bba,
                0xa75549f0, 0xd755aa72, 0xfb7e9908, 0x6844ade8, 0xa8b1b689,
                0x898aa733, 0x4a1db29d, 0x7684c27e, 0x74f0dc83, 0x7300e86f,
                0x0a47ce7a, 0x07f7b635, 0xb42e9894, 0x4414c04a, 0x1079982a,
                0x75a18fe6, 0x9217217b, 0xd2e6b201, 0xaa31b81a, 0x9f34c1d7,
                0x5de12a1e,

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
      public testing::WithParamInterface<RsaVerifyTestCase> {};

TEST_P(SigverifyRsaVerify, Ibex) {
  uint32_t flash_exec = 0;
  EXPECT_EQ(sigverify_rsa_verify(&GetParam().sig, GetParam().key, &kDigest,
                                 &flash_exec),
            kErrorOk);
  EXPECT_EQ(flash_exec, kSigverifyRsaSuccess);
}

INSTANTIATE_TEST_SUITE_P(AllCases, SigverifyRsaVerify,
                         testing::ValuesIn(kRsaVerifyTestCases));

}  // namespace
}  // namespace sigverify_keys_unittest
