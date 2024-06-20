// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace cert_unittest {
namespace {
using ::testing::_;
using ::testing::Return;
using ::testing::SetArgPointee;

class CertTest : public rom_test::RomTest {
 protected:
  uint8_t expected_sn_bytes_[kCertX509Asn1SerialNumberSizeInBytes] = {
      0x31, 0xF9, 0xE7, 0x35, 0x9F, 0xF2, 0x84, 0x46, 0x99, 0x5B,
      0xA0, 0x3D, 0xE5, 0xED, 0x7E, 0x32, 0x16, 0x95, 0xF1, 0xD1};
  uint32_t valid_dice_cert_words_[2048] = {
      0x1b038230, 0xc2028230, 0x010203a0, 0x31140202, 0x9f35e7f9, 0x994684f2,
      0xe53da05b, 0x16327eed, 0x30d1f195, 0x2a08060a, 0x3dce4886, 0x30020304,
      0x300b3123, 0x55030609, 0x02130604, 0x14314b55, 0x03061230, 0x0c030455,
      0x776f6c0b, 0x43534952, 0x43494320, 0x0f182230, 0x38313032, 0x32323330,
      0x39353332, 0x185a3935, 0x3939390f, 0x33323139, 0x35333231, 0x5a393539,
      0x31313330, 0x03062f30, 0x13050455, 0x66313328, 0x33376539, 0x66663935,
      0x34343832, 0x35393936, 0x33306162, 0x65356564, 0x33653764, 0x39363132,
      0x64316635, 0x30593031, 0x2a070613, 0x3dce4886, 0x08060102, 0xce48862a,
      0x0701033d, 0x04004203, 0x8d706f77, 0xe483013c, 0x7712eb41, 0x77324391,
      0x87759618, 0x637ff07c, 0x94703230, 0x425c9385, 0x4f6201c9, 0x7fb9b232,
      0x0d382d05, 0x13d677c4, 0xde831f4c, 0x9ef35ad2, 0xf6185161, 0x837a99cd,
      0xbe0182a3, 0xba018230, 0x03060f30, 0x01131d55, 0x0504ff01, 0x01010330,
      0x060f30ff, 0x0f1d5503, 0x04ff0101, 0x07030305, 0x22300004, 0x1d550306,
      0x00010123, 0x16301804, 0x22111480, 0x66554433, 0x11998877, 0x55443322,
      0x99887766, 0x20302211, 0x1d550306, 0x0001010e, 0x14041604, 0x35e7f931,
      0x4684f29f, 0x3da05b99, 0x327eede5, 0xd1f19516, 0x4e018230, 0x81670606,
      0x01040505, 0x04ff0101, 0x303f0182, 0x803b0182, 0x65704f09, 0x7469546e,
      0x06816e61, 0x69766544, 0x01836563, 0x00018400, 0x1a0182a6, 0x09062d30,
      0x01488660, 0x02040365, 0x41200401, 0x3cb6bbc3, 0x91b82cff, 0xf1dcba04,
      0x19d4e461, 0x25190a1a, 0x916b6459, 0xda0eab05, 0x3078bf51, 0x6009062d,
      0x65014886, 0x01020403, 0xbfac2004, 0x7e06c2a9, 0xf9cf1aca, 0x342a27eb,
      0x80bc0aa7, 0x88c75300, 0x4e952a62, 0x47bcfe0e, 0x2d309c7d, 0x86600906,
      0x03650148, 0x04010204, 0x2930f520, 0x06a7b225, 0xc22d94ad, 0x39f4fed4,
      0xf8db2f89, 0x9e813a3e, 0x75ea0986, 0x45ed09b7, 0x062d30a4, 0x48866009,
      0x04036501, 0x20040102, 0xf57adf1f, 0x3ceaa4a5, 0x94bce43f, 0xe027c121,
      0x33fc069d, 0x7487f3ae, 0xbf78e978, 0x2fe19e76, 0x09062d30, 0x01488660,
      0x02040365, 0x19200401, 0xc958c0e1, 0xb943daae, 0x5f7c542d, 0xf6c48ba6,
      0xeec1e294, 0x5b1a519d, 0xdc647a3b, 0x3037ef41, 0x6009062d, 0x65014886,
      0x01020403, 0x7d032004, 0xa29e2856, 0x302c577f, 0x8c90c942, 0x8b915a1d,
      0xbe878236, 0xe1e84c27, 0xe847c52d, 0x0287918f, 0x0a300004, 0x862a0806,
      0x043dce48, 0x47030203, 0x02443000, 0xd2bb3520, 0xbc8d82c0, 0xbf404f45,
      0x384855f2, 0x8ba5b0c8, 0x0698f275, 0x37d827c1, 0x3bee0f7d, 0x1d200289,
      0x533fe16b, 0xfa62b6b4, 0x46af0351, 0x3e262772, 0xe9d81a0b, 0x53859bf3,
      0x990281cf, 0x007897f8};
  uint8_t *valid_dice_cert_bytes_ = (uint8_t *)valid_dice_cert_words_;
  uint32_t expected_cert_size_ =
      ((valid_dice_cert_bytes_[2] << 8) | (valid_dice_cert_bytes_[3])) + 4;
};

TEST_F(CertTest, InvalidArgs) {
  hardened_bool_t matches = kHardenedBoolFalse;
  // Invalid cert page buffer.
  EXPECT_EQ(cert_x509_asn1_check_serial_number(nullptr, 0, expected_sn_bytes_,
                                               &matches, nullptr),
            kErrorCertInvalidArgument);

  // Invalid expected serial number.
  EXPECT_EQ(cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                               nullptr, &matches, nullptr),
            kErrorCertInvalidArgument);

  // Invalid match flag pointer.
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                         expected_sn_bytes_, nullptr, nullptr),
      kErrorCertInvalidArgument);

  // Invalid buffer offset.
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                valid_dice_cert_bytes_, FLASH_CTRL_PARAM_BYTES_PER_PAGE,
                expected_sn_bytes_, &matches, nullptr),
            kErrorCertInvalidArgument);
}

/**
 * Here we test if a flash page has been erased (i.e., is all 1s) but the page
 * has never been provisioned with a certificate.
 */
TEST_F(CertTest, UnprovisionedCert) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint32_t unprovisioned_cert_bytes = UINT32_MAX;
  uint32_t cert_size;
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                (uint8_t *)&unprovisioned_cert_bytes, 0, expected_sn_bytes_,
                &matches, &cert_size),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolFalse);
  EXPECT_EQ(cert_size, 0);
}

TEST_F(CertTest, BadSerialNumberTag) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t backup =
      valid_dice_cert_bytes_[kCertX509Asn1SerialNumberTagByteOffset];
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberTagByteOffset] = 0;
  EXPECT_DEATH(
      {OT_DISCARD(cert_x509_asn1_check_serial_number(
          valid_dice_cert_bytes_, 0, expected_sn_bytes_, &matches, nullptr))},
      "");
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberTagByteOffset] = backup;
}

TEST_F(CertTest, BadSerialNumberLength) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t backup =
      valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset];
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] = 22;
  EXPECT_DEATH(
      {OT_DISCARD(cert_x509_asn1_check_serial_number(
          valid_dice_cert_bytes_, 0, expected_sn_bytes_, &matches, nullptr))},
      "");
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] = backup;
}

TEST_F(CertTest, CertOutdated) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint32_t cert_size;
  uint8_t empty_sn[kCertX509Asn1SerialNumberSizeInBytes] = {0};
  EXPECT_EQ(cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                               empty_sn, &matches, &cert_size),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolFalse);
  EXPECT_EQ(cert_size, expected_cert_size_);
}

TEST_F(CertTest, CertOutdatedSerialNumberSizeMismatch) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t old_length =
      valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset];
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] = 19;
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                         expected_sn_bytes_, &matches, nullptr),
      kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolFalse);
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] =
      old_length;
}

TEST_F(CertTest, CertValidShortSerialNumber) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t old_length =
      valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset];
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] = 19;
  uint8_t sn_bytes[kCertX509Asn1SerialNumberSizeInBytes] = {0};
  memcpy(&sn_bytes[1], expected_sn_bytes_,
         kCertX509Asn1SerialNumberSizeInBytes - 1);
  EXPECT_EQ(cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                               sn_bytes, &matches, nullptr),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolTrue);
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] =
      old_length;
}

TEST_F(CertTest, CertValidFullSerialNumberThenShortSerialNumber) {
  hardened_bool_t matches = kHardenedBoolFalse;

  // Full length serial number.
  matches = kHardenedBoolFalse;
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                         expected_sn_bytes_, &matches, nullptr),
      kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolTrue);

  // Short length serial number.
  matches = kHardenedBoolFalse;
  uint8_t old_length =
      valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset];
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] = 19;
  uint8_t sn_bytes[kCertX509Asn1SerialNumberSizeInBytes] = {0};
  memcpy(&sn_bytes[1], expected_sn_bytes_,
         kCertX509Asn1SerialNumberSizeInBytes - 1);
  EXPECT_EQ(cert_x509_asn1_check_serial_number(valid_dice_cert_bytes_, 0,
                                               sn_bytes, &matches, nullptr),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolTrue);
  valid_dice_cert_bytes_[kCertX509Asn1SerialNumberLengthByteOffset] =
      old_length;
}

}  // namespace
}  // namespace cert_unittest
