// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include <cstring>
#include <numeric>
#include <unordered_set>

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/mock_sigverify_mod_exp_otbn.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/lib/sigverify_mod_exp.h"
#include "sw/device/silicon_creator/mask_rom/mock_sigverify_keys_ptrs.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys_ptrs.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "otp_ctrl_regs.h"

namespace sigverify_keys_unittest {
namespace {
using ::testing::Return;

/**
 * Mock keys used in tests.
 *
 * We only initialize the first word of `n`, which is the key ID, and `key_type`
 * since these are the only fields that are used for determining the validity of
 * a key. The remaining fields are initialized only because non-trivial
 * designated initializers are not supported.
 */
constexpr sigverify_mask_rom_key_t kMockKeys[]{
    {
        .key = {.n = {{0xA0}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeTest,
    },
    {
        .key = {.n = {{0xB0}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeProd,
    },
    {
        .key = {.n = {{0xC0}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeDev,
    },
    {
        .key = {.n = {{0xA1}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeTest,
    },
    {
        .key = {.n = {{0xB1}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeProd,
    },
    {
        .key = {.n = {{0xC1}}, .n0_inv = {0}, .exponent = 0},
        .key_type = kSigverifyKeyTypeDev,
    },
};
constexpr size_t kNumMockKeys = std::extent<decltype(kMockKeys)>::value;

/**
 * Returns the indices of mock keys of the given type.
 *
 * @param key_type A key type.
 * @return Indices of mock keys of the given type.
 */
std::vector<size_t> MockKeyIndicesOfType(sigverify_key_type_t key_type) {
  std::vector<size_t> indices;
  for (size_t i = 0; i < kNumMockKeys; ++i) {
    if (kMockKeys[i].key_type == key_type) {
      indices.push_back(i);
    }
  }
  return indices;
}

/**
 * Life cycle states used in parameterized tests.
 */

constexpr std::array<lifecycle_state_t, 8> kLcStatesTest{
    kLcStateTestUnlocked0, kLcStateTestUnlocked1, kLcStateTestUnlocked2,
    kLcStateTestUnlocked3, kLcStateTestUnlocked4, kLcStateTestUnlocked5,
    kLcStateTestUnlocked6, kLcStateTestUnlocked7,
};

constexpr std::array<lifecycle_state_t, 4> kLcStatesNonTestOperational{
    kLcStateDev,
    kLcStateProd,
    kLcStateProdEnd,
    kLcStateRma,
};

constexpr std::array<lifecycle_state_t, 12> kLcStatesNonOperational{
    kLcStateRaw,         kLcStateTestLocked0,
    kLcStateTestLocked1, kLcStateTestLocked2,
    kLcStateTestLocked3, kLcStateTestLocked4,
    kLcStateTestLocked5, kLcStateTestLocked6,
    kLcStateScrap,       kLcStatePostTransition,
    kLcStateEscalate,    kLcStateInvalid,
};

const std::unordered_set<lifecycle_state_t> &LcStatesAll() {
  static const std::unordered_set<lifecycle_state_t> *const kLcStatesAll =
      []() {
        auto states = new std::unordered_set<lifecycle_state_t>();
        states->insert(kLcStatesTest.begin(), kLcStatesTest.end());
        states->insert(kLcStatesNonTestOperational.begin(),
                       kLcStatesNonTestOperational.end());
        states->insert(kLcStatesNonOperational.begin(),
                       kLcStatesNonOperational.end());
        return states;
      }();
  return *kLcStatesAll;
}

TEST(LcStateCount, IsCorrect) {
  EXPECT_EQ(kLcStateNumStates, LcStatesAll().size());
}

class SigverifyKeys : public mask_rom_test::MaskRomTest {
 protected:
  /**
   * Sets expectations for getting the keys stored in the Mask ROM.
   *
   * @param keys An array of keys.
   */
  template <size_t N>
  void ExpectKeysPtrGet(const sigverify_mask_rom_key_t (&keys)[N]) {
    ASSERT_LE(N, OTP_CTRL_PARAM_CREATOR_SW_CFG_KEY_IS_VALID_SIZE);
    EXPECT_CALL(sigverify_keys_ptrs_, RsaKeysPtrGet()).WillOnce(Return(keys));
    EXPECT_CALL(sigverify_keys_ptrs_, NumRsaKeysGet()).WillOnce(Return(N));
  }

  /**
   * Sets an expectation for an OTP read for the key at the given index.
   *
   * The value that corresponds to `key_index` will be `is_valid` and the
   * values for all other keys in the corresponding OTP word will be the
   * complement of `is_valid`.
   *
   * @param key_index Index of a key.
   * @param is_valid Validitiy of the key.
   */
  void ExpectOtpRead(size_t key_index, hardened_byte_bool_t is_valid) {
    const uint32_t read_addr =
        OTP_CTRL_PARAM_CREATOR_SW_CFG_KEY_IS_VALID_OFFSET +
        (key_index / kSigverifyNumEntriesPerOtpWord) * sizeof(uint32_t);
    const size_t entry_index = key_index % kSigverifyNumEntriesPerOtpWord;

    std::array<uint8_t, kSigverifyNumEntriesPerOtpWord> entries;
    hardened_byte_bool_t others_val = is_valid == kHardenedByteBoolTrue
                                          ? kHardenedByteBoolFalse
                                          : kHardenedByteBoolTrue;
    entries.fill(others_val);
    entries[entry_index] = is_valid;

    uint32_t read_val;
    std::memcpy(&read_val, entries.data(), sizeof(read_val));
    EXPECT_CALL(otp_, read32(read_addr)).WillOnce(Return(read_val));
  }

  mask_rom_test::MockOtp otp_;
  mask_rom_test::MockSigverifyKeysPtrs sigverify_keys_ptrs_;
};

class BadKeyIdTypeTest : public SigverifyKeys,
                         public testing::WithParamInterface<lifecycle_state_t> {
};

TEST_P(BadKeyIdTypeTest, BadKeyId) {
  ExpectKeysPtrGet(kSigVerifyRsaKeys);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(0, GetParam(), &key), kErrorSigverifyBadKey);
}

TEST_P(BadKeyIdTypeTest, BadKeyType) {
  uint32_t key_id = 0xFF;
  sigverify_key_type_t bad_key_type =
      static_cast<sigverify_key_type_t>(kSigverifyKeyTypeDev + 1);
  sigverify_mask_rom_key_t keys[]{
      {
          .key = {.n = {{key_id}}, .n0_inv = {0}, .exponent = 0},
          .key_type = bad_key_type,
      },
  };

  ExpectKeysPtrGet(keys);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(key_id, GetParam(), &key),
            kErrorSigverifyBadKey);
}

INSTANTIATE_TEST_SUITE_P(AllLcStates, BadKeyIdTypeTest,
                         testing::ValuesIn(LcStatesAll()));

/**
 * Base class for paramaterized tests below.
 */
class KeyValidityTest : public SigverifyKeys,
                        public testing::WithParamInterface<
                            std::tuple<size_t, lifecycle_state_t>> {};

class NonOperationalState : public KeyValidityTest {};

TEST_P(NonOperationalState, BadKey) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysPtrGet(kMockKeys);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(
                sigverify_rsa_key_id_get(&kMockKeys[key_index].key.n), lc_state,
                &key),
            kErrorSigverifyBadKey);
}

INSTANTIATE_TEST_SUITE_P(
    AllKeysAndNonOperationalStates, NonOperationalState,
    testing::Combine(testing::Range<size_t>(0, kNumMockKeys),
                     testing::ValuesIn(kLcStatesNonOperational)));

class ValidBasedOnOtp : public KeyValidityTest {};

TEST_P(ValidBasedOnOtp, ValidInOtp) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysPtrGet(kMockKeys);
  ExpectOtpRead(key_index, kHardenedByteBoolTrue);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(
                sigverify_rsa_key_id_get(&kMockKeys[key_index].key.n), lc_state,
                &key),
            kErrorOk);
  EXPECT_EQ(key, &kMockKeys[key_index].key);
}

TEST_P(ValidBasedOnOtp, InvalidInOtp) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysPtrGet(kMockKeys);
  ExpectOtpRead(key_index, kHardenedByteBoolFalse);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(
                sigverify_rsa_key_id_get(&kMockKeys[key_index].key.n), lc_state,
                &key),
            kErrorSigverifyBadKey);
}

INSTANTIATE_TEST_SUITE_P(
    ProdKeysInNonTestStates, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeProd)),
        testing::ValuesIn(kLcStatesNonTestOperational)));

INSTANTIATE_TEST_SUITE_P(
    TestKeysInRmaState, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::Values(kLcStateRma)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysInDevState, ValidBasedOnOtp,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::Values(kLcStateDev)));

class ValidInState : public KeyValidityTest {};

TEST_P(ValidInState, Get) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysPtrGet(kMockKeys);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(
                sigverify_rsa_key_id_get(&kMockKeys[key_index].key.n), lc_state,
                &key),
            kErrorOk);
  EXPECT_EQ(key, &kMockKeys[key_index].key);
}

INSTANTIATE_TEST_SUITE_P(
    ProdKeysInTestStates, ValidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeProd)),
        testing::ValuesIn(kLcStatesTest)));

INSTANTIATE_TEST_SUITE_P(
    TestKeysInTestStates, ValidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::ValuesIn(kLcStatesTest)));

class InvalidInState : public KeyValidityTest {};

TEST_P(InvalidInState, Get) {
  size_t key_index;
  lifecycle_state_t lc_state;
  std::tie(key_index, lc_state) = GetParam();

  ExpectKeysPtrGet(kMockKeys);

  const sigverify_rsa_key_t *key;
  EXPECT_EQ(sigverify_rsa_key_get(
                sigverify_rsa_key_id_get(&kMockKeys[key_index].key.n), lc_state,
                &key),
            kErrorSigverifyBadKey);
}

INSTANTIATE_TEST_SUITE_P(
    TestKeysAndProdDevStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeTest)),
        testing::Values(kLcStateProd, kLcStateProdEnd, kLcStateDev)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysAndTestStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::ValuesIn(kLcStatesTest)));

INSTANTIATE_TEST_SUITE_P(
    DevKeysAndNonDevOperStates, InvalidInState,
    testing::Combine(
        testing::ValuesIn(MockKeyIndicesOfType(kSigverifyKeyTypeDev)),
        testing::Values(kLcStateProd, kLcStateProdEnd, kLcStateRma)));

TEST(Keys, UniqueIds) {
  std::unordered_set<uint32_t> ids;
  for (auto const &entry : kSigVerifyRsaKeys) {
    ids.insert(sigverify_rsa_key_id_get(&entry.key.n));
  }

  EXPECT_EQ(ids.size(), kSigVerifyNumRsaKeys);
}

// Note: The test cases below test sigverify using mask ROM keys. They have some
// overlap with sigverify_mod_exp_ibex unit tests but this way we don't have to
// worry about keeping the keys used in those tests in sync with mask ROM keys.

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

constexpr RsaVerifyTestCase kRsaVerifyTestCases[2]{
    // message: "test"
    {
        .key = &kSigVerifyRsaKeys[0].key,
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
    // message: "test"
    {
        .key = &kSigVerifyRsaKeys[1].key,
        .sig =
            {
                0xb13844fa, 0x9c7622d8, 0xda09bdc4, 0x79fde5c6, 0x7037a98b,
                0x4d53a5cf, 0xabd7e9e4, 0x8456c575, 0x1f1fc5f6, 0x7870e2d5,
                0x96a488c2, 0x7aa2263c, 0xbe5dbcf1, 0x34a6b2ff, 0x51bd23fa,
                0xef582d6d, 0x52d0e2fa, 0x586c6b2f, 0x0aa1e7d0, 0x0d1f8a33,
                0xf95e28bc, 0x70f13b45, 0x548740b0, 0x42be7f0d, 0x4254ac6f,
                0xb7363b68, 0x48f1c461, 0x06b8f936, 0xd3274353, 0x121219e4,
                0x98d8e770, 0x39e1bb17, 0x1a005ad4, 0x673985f4, 0x6f2cfd4a,
                0xba537c5f, 0x1ca6bdad, 0x5e7bdb7d, 0x9b6783bd, 0xf3a1e998,
                0xa5dc56f6, 0x149d6bb5, 0x9437917a, 0xfeb89880, 0x6e6ce5f9,
                0x07bece66, 0xaab327ae, 0x1ff13a9e, 0x35e3b280, 0x645b636a,
                0x34628104, 0xda8148ee, 0x95d22ce1, 0x78f4e1a0, 0xec9bdf2e,
                0x42fc69d0, 0x4b8e5244, 0x192a0454, 0x7bfd31dc, 0x09a07d77,
                0x2a3c745b, 0x8d5deeb7, 0xb539505c, 0xd5352a21, 0x22fd9774,
                0x6fd4f48f, 0x60d2c5e9, 0x9292c725, 0x035797d8, 0x8bbb8d02,
                0x977bdd02, 0x2da179b2, 0xa9779cc9, 0x13c5fe29, 0x607c3673,
                0x8e52aeca, 0x6fd9ea3a, 0x5915a281, 0x69dc74c2, 0x162207fb,
                0x1efa0497, 0x0a9e1a61, 0x3542ac58, 0x885d5d5e, 0x29623b26,
                0x14cbc783, 0xa2f9511e, 0xfcb8986f, 0x6b7ca8d8, 0xde4c53b2,
                0x4f8fd997, 0x2eded334, 0xe9d492dd, 0xd0751bc1, 0x9077d8cd,
                0x5563ec91,
            },
    },
};

TEST(RsaVerifyTestCases, AllKeys) {
  std::unordered_set<uint32_t> ids;
  for (auto const &test_case : kRsaVerifyTestCases) {
    ids.insert(sigverify_rsa_key_id_get(&test_case.key->n));
  }

  EXPECT_EQ(ids.size(), kSigVerifyNumRsaKeys);
}

class SigverifyRsaVerify
    : public mask_rom_test::MaskRomTest,
      public testing::WithParamInterface<RsaVerifyTestCase> {
 protected:
  mask_rom_test::MockOtp otp_;
};

TEST_P(SigverifyRsaVerify, Ibex) {
  EXPECT_CALL(otp_,
              read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_USE_SW_RSA_VERIFY_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));

  EXPECT_EQ(sigverify_rsa_verify(&GetParam().sig, GetParam().key, &kDigest,
                                 kLcStateProd),
            kErrorOk);
}

INSTANTIATE_TEST_SUITE_P(AllCases, SigverifyRsaVerify,
                         testing::ValuesIn(kRsaVerifyTestCases));

}  // namespace
}  // namespace sigverify_keys_unittest
