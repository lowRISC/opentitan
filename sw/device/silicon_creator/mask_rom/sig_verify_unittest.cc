// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sig_verify.h"

#include <cstring>

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "sig_verify_keys.h"
#include "sw/device/silicon_creator/lib/drivers/mock_hmac.h"
#include "sw/device/silicon_creator/mask_rom/mock_rsa_verify.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace sig_verify_unittest {
namespace {
using ::testing::DoAll;
using ::testing::NotNull;
using ::testing::Pointee;
using ::testing::Return;
using ::testing::SetArgPointee;

/**
 * SHA2-256 digest of "test".
 *
 * Can be obtained using:
 * ```
 * echo -n "test" | openssl dgst -sha256 -binary | \
 *    xxd -p -c 4 | tac | sed 's|.*|0x&,|'
 * ```
 */
constexpr hmac_digest_t kTestDigest{
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
 * 3072-bit EMSA-PKCS1-v1_5 encoding of `kTestDigest`.
 *
 * Can be obtained using:
 * ```
 * # Create private key.
 * openssl genrsa -out key.pem 3072
 * # Sign.
 * echo -n "test" | openssl dgst -sha256 -sign key.pem -out signature
 * # Print encoded message.
 * openssl rsautl -verify -in signature -inkey key.pem -raw | \
 *    xxd -p -c 4 | tac | sed 's|.*|0x&,|'
 * ```
 */
constexpr sigverify_rsa_buffer_t kEncMsg{
    .data = {
        0xb0f00a08, 0xd15d6c15, 0x2b0b822c, 0xa3bf4f1b, 0xc55ad015, 0x9a2feaa0,
        0x884c7d65, 0x9f86d081, 0x05000420, 0x03040201, 0x86480165, 0x0d060960,
        0x00303130, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0x0001ffff,
    }};

// The contents of `kSignedRegion` and `kSignature` are not significant since we
// use mocks. `kSignedRegion` is initialized this way only for consistency with
// `kTestDigest`.
// TODO(opentitan/#5955): Remove when the manifest struct is ready and
// `sigverify_rom_ext_signature_check` is updated.
constexpr std::array<uint8_t, 4> kSignedRegion{'t', 'e', 's', 't'};
constexpr sigverify_rsa_buffer_t kSignature{};

class SigVerifyTest : public mask_rom_test::MaskRomTest {
 protected:
  mask_rom_test::MockRsaVerify sig_verify_mod_exp_;
  mask_rom_test::MockHmac hmac_;
};

TEST_F(SigVerifyTest, GoodSignature) {
  // FIXME: Parameterize with key ids.
  const auto key_id = sigverify_rsa_key_id_get(&kSigVerifyRsaKeys[0]);

  EXPECT_CALL(hmac_, sha256_init());
  EXPECT_CALL(hmac_, sha256_update(kSignedRegion.data(), sizeof(kSignedRegion)))
      .WillOnce(Return(kErrorOk));
  EXPECT_CALL(hmac_, sha256_final(NotNull()))
      .WillOnce(DoAll(SetArgPointee<0>(kTestDigest), Return(kErrorOk)));
  EXPECT_CALL(sig_verify_mod_exp_,
              mod_exp_ibex(&kSigVerifyRsaKeys[0], &kSignature, NotNull()))
      .WillOnce(DoAll(SetArgPointee<2>(kEncMsg), Return(kErrorOk)));

  EXPECT_EQ(
      sigverify_rom_ext_signature_verify(
          kSignedRegion.data(), sizeof(kSignedRegion), &kSignature, key_id),
      kErrorOk);
}

TEST_F(SigVerifyTest, BadSignature) {
  // FIXME: Parameterize with key ids.
  const auto key_id = sigverify_rsa_key_id_get(&kSigVerifyRsaKeys[0]);

  // Corrupt the words of the encoded message by flipping their bits and check
  // that signature verification fails.
  // FIXME: Make this a parameterized test.
  for (size_t i = 0; i < kSigVerifyRsaNumWords; ++i) {
    auto bad_enc_msg = kEncMsg;
    bad_enc_msg.data[i] = ~bad_enc_msg.data[i];

    EXPECT_CALL(hmac_, sha256_init());
    EXPECT_CALL(hmac_,
                sha256_update(kSignedRegion.data(), sizeof(kSignedRegion)))
        .WillOnce(Return(kErrorOk));
    EXPECT_CALL(hmac_, sha256_final(NotNull()))
        .WillOnce(DoAll(SetArgPointee<0>(kTestDigest), Return(kErrorOk)));
    EXPECT_CALL(sig_verify_mod_exp_,
                mod_exp_ibex(&kSigVerifyRsaKeys[0], &kSignature, NotNull()))
        .WillOnce(DoAll(SetArgPointee<2>(bad_enc_msg), Return(true)));

    EXPECT_EQ(
        sigverify_rom_ext_signature_verify(
            kSignedRegion.data(), sizeof(kSignedRegion), &kSignature, key_id),
        kErrorSigverifyInvalidArgument);
  }
}

}  // namespace
}  // namespace sig_verify_unittest
