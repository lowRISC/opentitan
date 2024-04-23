// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
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
  flash_ctrl_error_code_t flash_ctrl_error_code_ = {
      .macro_err = false,
      .update_err = false,
      .prog_type_err = false,
      .prog_win_err = false,
      .prog_err = false,
      .rd_err = false,
      .mp_err = false,
      .op_err = false,
  };
  uint32_t expected_sn_words_[kCertX509Asn1SerialNumberSizeIn32BitWords] = {
      0xb70ac90a, 0x74193c67, 0x49ca1b80, 0x77e3b46e, 0xcd20ea3b,
  };
  static constexpr size_t kDiceCertSizeInBytes =
      kCertX509Asn1FirstWordsWithSerialNumber * sizeof(uint32_t);
  uint32_t valid_dice_cert_words_[200] = {
      0x1d038230, 0xc2028230, 0x010203a0, 0x0a140202, 0x67b70ac9, 0x8074193c,
      0x6e49ca1b, 0x3b77e3b4, 0x30cd20ea, 0x2a08060a, 0x3dce4886, 0x30020304,
      0x30143123, 0x55030612, 0x0b0c0304, 0x52776f6c, 0x20435349, 0x31434943,
      0x0609300b, 0x06045503, 0x4b550213, 0x0f182230, 0x38313032, 0x32323330,
      0x39353332, 0x185a3935, 0x3939390f, 0x33323139, 0x35333231, 0x5a393539,
      0x31313330, 0x03062f30, 0x13050455, 0x63613028, 0x62613039, 0x33373637,
      0x37393163, 0x31303834, 0x34616362, 0x62653639, 0x37336534, 0x65623337,
      0x63303261, 0x30593064, 0x2a070613, 0x3dce4886, 0x08060102, 0xce48862a,
      0x0701033d, 0x04004203, 0x593c01be, 0x8d03adc8, 0x1bcec8bb, 0x7bed6cfd,
      0x276ffc41, 0x7dfcf3e6, 0x083d1b45, 0x6de39fbd, 0xbc14a18c, 0x468186e4,
      0xdd1a53c2, 0x11dd94ab, 0x1eaec3cd, 0xd1c1a4c1, 0xc4224618, 0xe857939c,
      0xbe0182a3, 0xba018230, 0x03060f30, 0x01131d55, 0x0504ff01, 0x01010330,
      0x060f30ff, 0x0f1d5503, 0x04ff0101, 0x07030305, 0x22300004, 0x1d550306,
      0x00010123, 0x16301804, 0x22111480, 0x66554433, 0x11998877, 0x55443322,
      0x99887766, 0x20302211, 0x1d550306, 0x0001010e, 0x14041604, 0xb70ac90a,
      0x74193c67, 0x49ca1b80, 0x77e3b46e, 0xcd20ea3b, 0x4e018230, 0x81670606,
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
      0x043dce48, 0x49030203, 0x02463000, 0xddfd0021, 0xe563cd18, 0x2cc4157d,
      0x6b3e905d, 0x77c58c5d, 0xb2682329, 0xdfa9ef3b, 0x6bf5fd60, 0x2102a780,
      0x0d849c00, 0xf9d9ab8f, 0x1e7f5774, 0x16e331d1, 0xd3c98359, 0x79a50f16,
      0x8871f9d9, 0x0b588f5b,
  };
  rom_test::MockFlashCtrl flash_ctrl_;
  void ExpectFlashInfoPageRead(const flash_ctrl_info_page_t *info_page,
                               uint32_t offset, size_t num_words,
                               const uint32_t *data, rom_error_t error) {
    EXPECT_CALL(flash_ctrl_, InfoRead(info_page, offset, num_words, _))
        .WillOnce([num_words, data, error](auto, auto, auto, void *out) {
          uint32_t *out_words = static_cast<uint32_t *>(out);
          for (size_t i = 0; i < num_words; ++i) {
            out_words[i] = data[i];
          }
          return error;
        });
  }
  void ExpectFlashCtrlErrorCodeGet(flash_ctrl_error_code_t *in_error_code) {
    EXPECT_CALL(flash_ctrl_, ErrorCodeGet(_))
        .WillOnce(SetArgPointee<0>(*in_error_code));
  }
  void ExpectFlashInfoPageErase(const flash_ctrl_info_page_t *info_page,
                                rom_error_t error) {
    EXPECT_CALL(flash_ctrl_, InfoErase(info_page, kFlashCtrlEraseTypePage))
        .WillOnce(Return(error));
  }
};

TEST_F(CertTest, InvalidArgs) {
  hardened_bool_t matches = kHardenedBoolFalse;
  // Invalid flash info page.
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(nullptr, expected_sn_words_, &matches),
      kErrorCertInvalidArgument);

  // Invalid expected serial number.
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                &kFlashCtrlInfoPageUdsCertificate, nullptr, &matches),
            kErrorCertInvalidArgument);

  // Invalid match flag pointer.
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                &kFlashCtrlInfoPageUdsCertificate, expected_sn_words_, nullptr),
            kErrorCertInvalidArgument);
}

/**
 * Here we test if the a flash page looks like garbage as scrambling is enabled
 * but the page has never been erased.
 */
TEST_F(CertTest, CorruptedOrUnprovisionedCertFlashInfoPage) {
  hardened_bool_t matches = kHardenedBoolFalse;
  flash_ctrl_error_code_.rd_err = true;
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          valid_dice_cert_words_, kErrorFlashCtrlInfoRead);
  ExpectFlashCtrlErrorCodeGet(&flash_ctrl_error_code_);
  ExpectFlashInfoPageErase(&kFlashCtrlInfoPageUdsCertificate, kErrorOk);
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(&kFlashCtrlInfoPageUdsCertificate,
                                         expected_sn_words_, &matches),
      kErrorOk);
  flash_ctrl_error_code_.rd_err = false;
}

/**
 * Here we test if the a flash page has been erased (i.e., is all 1s) but the
 * page has never been provisioned with a certificate.
 */
TEST_F(CertTest, UnprovisionedCertFlashInfoPage) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t unprovisioned_cert_bytes[kDiceCertSizeInBytes] = {0};
  unprovisioned_cert_bytes[0] = 0xFF;
  unprovisioned_cert_bytes[1] = 0xFF;
  unprovisioned_cert_bytes[2] = 0xFF;
  unprovisioned_cert_bytes[3] = 0xFF;
  unprovisioned_cert_bytes[kCertX509Asn1FirstBytesWithSerialNumber - 4] = 0xFF;
  unprovisioned_cert_bytes[kCertX509Asn1FirstBytesWithSerialNumber - 3] = 0xFF;
  unprovisioned_cert_bytes[kCertX509Asn1FirstBytesWithSerialNumber - 2] = 0xFF;
  unprovisioned_cert_bytes[kCertX509Asn1FirstBytesWithSerialNumber - 1] = 0xFF;
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          (uint32_t *)unprovisioned_cert_bytes, kErrorOk);
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(&kFlashCtrlInfoPageUdsCertificate,
                                         expected_sn_words_, &matches),
      kErrorOk);
}

TEST_F(CertTest, BadSerialNumberTag) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t invalid_dice_cert_bytes[kDiceCertSizeInBytes] = {0};
  EXPECT_DEATH(
      {
        ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                                /*offset=*/0,
                                kCertX509Asn1FirstWordsWithSerialNumber,
                                (uint32_t *)invalid_dice_cert_bytes, kErrorOk);
        OT_DISCARD(cert_x509_asn1_check_serial_number(
            &kFlashCtrlInfoPageUdsCertificate, expected_sn_words_, &matches))
      },
      "");
}

TEST_F(CertTest, BadSerialNumberLength) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint8_t invalid_dice_cert_bytes[kDiceCertSizeInBytes] = {0};
  invalid_dice_cert_bytes[kCertX509Asn1SerialNumberByteOffset] = 0x02;
  EXPECT_DEATH(
      {
        ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                                /*offset=*/0,
                                kCertX509Asn1FirstWordsWithSerialNumber,
                                (uint32_t *)invalid_dice_cert_bytes, kErrorOk);
        OT_DISCARD(cert_x509_asn1_check_serial_number(
            &kFlashCtrlInfoPageUdsCertificate, expected_sn_words_, &matches))
      },
      "");
}

TEST_F(CertTest, CertOutdated) {
  hardened_bool_t matches = kHardenedBoolFalse;
  uint32_t empty_sn[kCertX509Asn1SerialNumberSizeIn32BitWords] = {0};
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          valid_dice_cert_words_, kErrorOk);
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                &kFlashCtrlInfoPageUdsCertificate, empty_sn, &matches),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolFalse);
}

TEST_F(CertTest, CertValid) {
  hardened_bool_t matches = kHardenedBoolFalse;
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          valid_dice_cert_words_, kErrorOk);
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(&kFlashCtrlInfoPageUdsCertificate,
                                         expected_sn_words_, &matches),
      kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolTrue);
}

}  // namespace
}  // namespace cert_unittest
