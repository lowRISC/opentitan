// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/cert/asn1.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

static uint8_t actual_serial_number[kCertX509Asn1SerialNumberSizeInBytes] = {0};

uint32_t cert_x509_asn1_decode_size_header(const uint8_t *header) {
  if (header[0] != 0x30 || header[1] != 0x82) {
    return 0;
  }
  return (((uint32_t)header[2]) << 8) + header[3] + 4 /* size of the header */;
}

rom_error_t cert_x509_asn1_get_size_in_bytes(
    const flash_ctrl_info_page_t *info_page, uint32_t offset, uint32_t *size) {
  uint8_t asn1_header[sizeof(uint32_t)];
  RETURN_IF_ERROR(
      flash_ctrl_info_read(info_page, offset, /*word_count=*/1, &asn1_header));
  *size = cert_x509_asn1_decode_size_header(asn1_header);
  if (*size == 0) {
    return kErrorCertInvalidSize;
  }
  return kErrorOk;
}

rom_error_t cert_x509_asn1_check_serial_number(
    const flash_ctrl_info_page_t *info_page, uint8_t *expected_sn_bytes,
    hardened_bool_t *matches) {
  if (info_page == NULL || expected_sn_bytes == NULL || matches == NULL) {
    return kErrorCertInvalidArgument;
  }
  *matches = kHardenedBoolFalse;

  // Read first part of certificate, up to, and including, the serial number.
  uint32_t cert_words[kCertX509Asn1FirstWordsWithSerialNumber] = {0};
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

  // Check if the cert is missing by checking if the first and last words are
  // all 1s. If it is, it because the device is unprovisioned, in which case, we
  // want to continue, and allow the ROM_EXT to attempt to update the cert.
  if (launder32(cert_words[0]) == UINT32_MAX) {
    HARDENED_CHECK_EQ(cert_words[0], UINT32_MAX);
    if (launder32(cert_words[kCertX509Asn1FirstWordsWithSerialNumber - 1]) ==
        UINT32_MAX) {
      HARDENED_CHECK_EQ(cert_words[kCertX509Asn1FirstWordsWithSerialNumber - 1],
                        UINT32_MAX);
      return kErrorOk;
    }
  }

  // Extract tag and length of serial number field.
  unsigned char *cert_bytes = (unsigned char *)cert_words;
  uint8_t asn1_tag = cert_bytes[kCertX509Asn1SerialNumberTagByteOffset];
  size_t asn1_integer_length =
      cert_bytes[kCertX509Asn1SerialNumberLengthByteOffset];

  // Validate tag and length values.
  // Tag should be 0x2 (the ASN.1 tag for an INTEGER).
  HARDENED_CHECK_EQ(asn1_tag, kAsn1TagNumberInteger);
  // Length should be less than or equal to 21 bytes (if the MSb of the
  // measurement is 1, a zero is added during ASN.1 encoding since the value is
  // unsigned), as specified in IETF RFC 5280, and hardcoded in the certificate
  // HJSON specifications.
  HARDENED_CHECK_LE(asn1_integer_length,
                    kCertX509Asn1SerialNumberSizeInBytes + 1);

  // If the length is 21 bytes, we skip the first 0 pad byte.
  size_t sn_bytes_offset = kCertX509Asn1SerialNumberLengthByteOffset + 1;
  if (launder32(asn1_integer_length) ==
      kCertX509Asn1SerialNumberSizeInBytes + 1) {
    HARDENED_CHECK_EQ(asn1_integer_length,
                      kCertX509Asn1SerialNumberSizeInBytes + 1);
    sn_bytes_offset++;
    asn1_integer_length--;
  }

  // Extract serial number bytes from the certificate into a 20-byte array as
  // this is the full size of the serial number integer.
  //
  // We fill the end of the array to ensure we maintain any prefix zero padding.
  //
  // We make sure to clear out the staging buffer before copying the actual cert
  // bytes in case this function was previously called on a cert that had a
  // larger serial number than currently present.
  memset(actual_serial_number, 0, kCertX509Asn1SerialNumberSizeInBytes);
  memcpy(&actual_serial_number[kCertX509Asn1SerialNumberSizeInBytes -
                               asn1_integer_length],
         &cert_bytes[sn_bytes_offset], asn1_integer_length);

  // Check the serial number in the certificate matches what was expected.
  *matches = kHardenedBoolFalse;
  for (size_t i = 0; i < kCertX509Asn1SerialNumberSizeInBytes; ++i) {
    if (launder32(actual_serial_number[i]) != expected_sn_bytes[i]) {
      HARDENED_CHECK_NE(actual_serial_number[i], expected_sn_bytes[i]);
      return kErrorOk;
    }
  }

  *matches = kHardenedBoolTrue;

  return kErrorOk;
}
