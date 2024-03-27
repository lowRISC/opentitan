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
      0xDE595D6D, 0x4209A128, 0x2ECC45C4, 0xB1588428, 0x90B7A35C,
  };
  static constexpr size_t kDiceCertSizeInBytes = 801;
  uint8_t valid_dice_cert_bytes_[kDiceCertSizeInBytes] = {
      48,  130, 3,   29,  48,  130, 2,   195, 160, 3,   2,   1,   2,   2,   21,
      0,   222, 89,  93,  109, 66,  9,   161, 40,  46,  204, 69,  196, 177, 88,
      132, 40,  144, 183, 163, 92,  48,  10,  6,   8,   42,  134, 72,  206, 61,
      4,   3,   2,   48,  35,  49,  20,  48,  18,  6,   3,   85,  4,   3,   12,
      11,  108, 111, 119, 82,  73,  83,  67,  32,  67,  73,  67,  49,  11,  48,
      9,   6,   3,   85,  4,   6,   19,  2,   85,  75,  48,  34,  24,  15,  50,
      48,  49,  56,  48,  51,  50,  50,  50,  51,  53,  57,  53,  57,  90,  24,
      15,  57,  57,  57,  57,  49,  50,  51,  49,  50,  51,  53,  57,  53,  57,
      90,  48,  51,  49,  49,  48,  47,  6,   3,   85,  4,   5,   19,  40,  100,
      101, 53,  57,  53,  100, 54,  100, 52,  50,  48,  57,  97,  49,  50,  56,
      50,  101, 99,  99,  52,  53,  99,  52,  98,  49,  53,  56,  56,  52,  50,
      56,  57,  48,  98,  55,  97,  51,  53,  99,  48,  89,  48,  19,  6,   7,
      42,  134, 72,  206, 61,  2,   1,   6,   8,   42,  134, 72,  206, 61,  3,
      1,   7,   3,   66,  0,   4,   166, 216, 6,   171, 245, 43,  85,  149, 51,
      175, 190, 73,  216, 70,  114, 123, 124, 131, 69,  23,  42,  209, 23,  255,
      248, 34,  94,  167, 135, 0,   179, 89,  145, 8,   185, 194, 68,  239, 24,
      117, 247, 24,  247, 179, 182, 134, 247, 129, 209, 19,  182, 167, 226, 169,
      84,  82,  162, 165, 130, 89,  166, 158, 121, 139, 163, 130, 1,   190, 48,
      130, 1,   186, 48,  15,  6,   3,   85,  29,  19,  1,   1,   255, 4,   5,
      48,  3,   1,   1,   255, 48,  15,  6,   3,   85,  29,  15,  1,   1,   255,
      4,   5,   3,   3,   7,   4,   0,   48,  34,  6,   3,   85,  29,  35,  1,
      1,   0,   4,   24,  48,  22,  128, 20,  17,  34,  51,  68,  85,  102, 119,
      136, 153, 17,  34,  51,  68,  85,  102, 119, 136, 153, 17,  34,  48,  32,
      6,   3,   85,  29,  14,  1,   1,   0,   4,   22,  4,   20,  222, 89,  93,
      109, 66,  9,   161, 40,  46,  204, 69,  196, 177, 88,  132, 40,  144, 183,
      163, 92,  48,  130, 1,   78,  6,   6,   103, 129, 5,   5,   4,   1,   1,
      1,   255, 4,   130, 1,   63,  48,  130, 1,   59,  128, 9,   79,  112, 101,
      110, 84,  105, 116, 97,  110, 129, 6,   68,  101, 118, 105, 99,  101, 131,
      1,   0,   132, 1,   0,   166, 130, 1,   26,  48,  45,  6,   9,   96,  134,
      72,  1,   101, 3,   4,   2,   1,   4,   32,  65,  195, 187, 182, 60,  255,
      44,  184, 145, 4,   186, 220, 241, 97,  228, 212, 25,  26,  10,  25,  37,
      89,  100, 107, 145, 5,   171, 14,  218, 81,  191, 120, 48,  45,  6,   9,
      96,  134, 72,  1,   101, 3,   4,   2,   1,   4,   32,  172, 191, 169, 194,
      6,   126, 202, 26,  207, 249, 235, 39,  42,  52,  167, 10,  188, 128, 0,
      83,  199, 136, 98,  42,  149, 78,  14,  254, 188, 71,  125, 156, 48,  45,
      6,   9,   96,  134, 72,  1,   101, 3,   4,   2,   1,   4,   32,  247, 253,
      170, 31,  253, 52,  30,  111, 225, 72,  186, 222, 117, 125, 50,  179, 33,
      188, 139, 1,   83,  45,  177, 102, 64,  253, 2,   67,  220, 130, 95,  16,
      48,  45,  6,   9,   96,  134, 72,  1,   101, 3,   4,   2,   1,   4,   32,
      120, 3,   216, 254, 55,  169, 3,   189, 9,   32,  255, 218, 100, 86,  54,
      17,  26,  207, 200, 206, 77,  47,  165, 203, 170, 199, 89,  177, 202, 56,
      147, 238, 48,  45,  6,   9,   96,  134, 72,  1,   101, 3,   4,   2,   1,
      4,   32,  25,  225, 192, 88,  201, 174, 218, 67,  185, 45,  84,  124, 95,
      166, 139, 196, 246, 148, 226, 193, 238, 157, 81,  26,  91,  59,  122, 100,
      220, 65,  239, 55,  48,  45,  6,   9,   96,  134, 72,  1,   101, 3,   4,
      2,   1,   4,   32,  3,   125, 86,  40,  158, 162, 127, 87,  44,  48,  66,
      201, 144, 140, 29,  90,  145, 139, 54,  130, 135, 190, 39,  76,  232, 225,
      45,  197, 71,  232, 143, 145, 135, 2,   4,   0,   48,  10,  6,   8,   42,
      134, 72,  206, 61,  4,   3,   2,   3,   72,  0,   48,  69,  2,   32,  77,
      146, 90,  183, 96,  93,  116, 156, 76,  17,  247, 35,  154, 87,  22,  182,
      3,   105, 150, 122, 252, 126, 63,  112, 192, 220, 51,  71,  88,  105, 4,
      10,  2,   33,  0,   254, 51,  54,  114, 51,  65,  213, 244, 203, 189, 99,
      51,  205, 78,  32,  77,  84,  45,  131, 156, 199, 217, 136, 120, 47,  201,
      46,  94,  89,  107, 136, 215,
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

TEST_F(CertTest, UnprovisionedCertFlashInfoPage) {
  hardened_bool_t matches = kHardenedBoolFalse;
  flash_ctrl_error_code_.rd_err = true;
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          (uint32_t *)valid_dice_cert_bytes_,
                          kErrorFlashCtrlInfoRead);
  ExpectFlashCtrlErrorCodeGet(&flash_ctrl_error_code_);
  ExpectFlashInfoPageErase(&kFlashCtrlInfoPageUdsCertificate, kErrorOk);
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(&kFlashCtrlInfoPageUdsCertificate,
                                         expected_sn_words_, &matches),
      kErrorCertCorrupted);
  flash_ctrl_error_code_.rd_err = false;
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
                          (uint32_t *)valid_dice_cert_bytes_, kErrorOk);
  EXPECT_EQ(cert_x509_asn1_check_serial_number(
                &kFlashCtrlInfoPageUdsCertificate, empty_sn, &matches),
            kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolFalse);
}

TEST_F(CertTest, CertValid) {
  hardened_bool_t matches = kHardenedBoolFalse;
  ExpectFlashInfoPageRead(&kFlashCtrlInfoPageUdsCertificate,
                          /*offset=*/0, kCertX509Asn1FirstWordsWithSerialNumber,
                          (uint32_t *)valid_dice_cert_bytes_, kErrorOk);
  EXPECT_EQ(
      cert_x509_asn1_check_serial_number(&kFlashCtrlInfoPageUdsCertificate,
                                         expected_sn_words_, &matches),
      kErrorOk);
  EXPECT_EQ(matches, kHardenedBoolTrue);
}

}  // namespace
}  // namespace cert_unittest
