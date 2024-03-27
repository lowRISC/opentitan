// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Offset to the ASN.1 DER encoded serial number of an X.509 certificate.
   */
  kCertX509Asn1SerialNumberByteOffset = 13,

  /**
   * Sizes of the ASN.1 DER encoded serial number of an X.509 certificate.
   */
  kCertX509Asn1SerialNumberSizeInBytes = 20,
  kCertX509Asn1SerialNumberSizeIn32BitWords =
      kCertX509Asn1SerialNumberSizeInBytes / sizeof(uint32_t),

  /**
   * Number of words/bytes of an X.509 ASN.1 DER encoded certificate up to, and
   * including, the serial number.
   */
  kCertX509Asn1FirstBytesWithSerialNumber =
      kCertX509Asn1SerialNumberByteOffset +
      kCertX509Asn1SerialNumberSizeInBytes + sizeof(uint32_t) - 1,
  kCertX509Asn1FirstWordsWithSerialNumber =
      kCertX509Asn1FirstBytesWithSerialNumber / sizeof(uint32_t),
};

/**
 * Extracts the serial number field from an ASN.1 DER encoded X.509 certificate
 * and checks if it matches what is expected.
 *
 * @param info_page Pointer to the flash info page the certificate is on.
 * @param expected_sn_words Expected serial number words (in big endian order).
 * @param[out] matches True if expected serial number found. False otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t cert_x509_asn1_check_serial_number(
    const flash_ctrl_info_page_t *info_page, uint32_t *expected_sn_words,
    hardened_bool_t *matches);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
