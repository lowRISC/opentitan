// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/cert/asn1.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

rom_error_t cert_x509_asn1_check_serial_number(
    const flash_ctrl_info_page_t *info_page, uint32_t *expected_sn_words,
    hardened_bool_t *matches) {
  if (info_page == NULL || expected_sn_words == NULL || matches == NULL) {
    return kErrorCertInvalidArgument;
  }
  *matches = kHardenedBoolFalse;

  // Read first part of certificate, up to, and including, the serial number.
  uint32_t cert_words[kCertX509Asn1FirstBytesWithSerialNumber] = {0};
  rom_error_t err = flash_ctrl_info_read(
      info_page, /*offset=*/0,
      /*word_count=*/kCertX509Asn1FirstWordsWithSerialNumber, cert_words);
  if (err != kErrorOk) {
    flash_ctrl_error_code_t flash_ctrl_err_code;
    flash_ctrl_error_code_get(&flash_ctrl_err_code);
    if (flash_ctrl_err_code.rd_err) {
      // If we encountered a read error, this could mean the certificate page
      // has been corrupted or is not provisioned yet. In this case, we erase
      // the page and continue, which will simply result in the ROM_EXT
      // re-generating the certificates.
      HARDENED_RETURN_IF_ERROR(
          flash_ctrl_info_erase(info_page, kFlashCtrlEraseTypePage));
      return kErrorOk;
    }
    return err;
  }

  // Extract tag and length.
  unsigned char *cert_bytes = (unsigned char *)cert_words;
  uint8_t asn1_tag = cert_bytes[kCertX509Asn1SerialNumberByteOffset];
  size_t asn1_integer_length =
      cert_bytes[kCertX509Asn1SerialNumberByteOffset + 1];

  // Validate tag and length values.
  // Tag should be 0x2 (the ASN.1 tag for an INTEGER).
  HARDENED_CHECK_EQ(asn1_tag, kAsn1TagNumberInteger);
  // Length should be 20 or 21 bytes (depending on if the MSb of the measurement
  // is 1 since the value is unsigned), as specified in IETF RFC 5280, and
  // hardcoded in the certificate HJSON specifications.
  HARDENED_CHECK_GE(asn1_integer_length, kCertX509Asn1SerialNumberSizeInBytes);
  HARDENED_CHECK_LE(asn1_integer_length,
                    kCertX509Asn1SerialNumberSizeInBytes + 1);

  // Check the serial number in the certificate matches what was expected.
  size_t sn_bytes_offset = kCertX509Asn1SerialNumberByteOffset + 2;
  if (launder32(asn1_integer_length) ==
      kCertX509Asn1SerialNumberSizeInBytes + 1) {
    HARDENED_CHECK_EQ(asn1_integer_length,
                      kCertX509Asn1SerialNumberSizeInBytes + 1);
    sn_bytes_offset++;
  }
  uint32_t curr_sn_word = 0;
  for (size_t i = 0; i < kCertX509Asn1SerialNumberSizeIn32BitWords; ++i) {
    curr_sn_word = 0;
    for (size_t j = 0; j < sizeof(uint32_t); ++j) {
      curr_sn_word = (curr_sn_word << 8) |
                     cert_bytes[sn_bytes_offset + (i * sizeof(uint32_t)) + j];
    }
    if (launder32(curr_sn_word) != expected_sn_words[i]) {
      HARDENED_CHECK_NE(curr_sn_word, expected_sn_words[i]);
      return kErrorOk;
    }
  }

  *matches = kHardenedBoolTrue;

  return kErrorOk;
}
