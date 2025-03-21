// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Offsets to the ASN.1 DER encoded serial number of an X.509 certificate.
   */
  kCertX509Asn1SerialNumberFieldByteOffset = 13,
  kCertX509Asn1SerialNumberTagByteOffset =
      kCertX509Asn1SerialNumberFieldByteOffset,
  kCertX509Asn1SerialNumberLengthByteOffset =
      kCertX509Asn1SerialNumberTagByteOffset + 1,

  /**
   * Sizes of the ASN.1 DER encoded serial number of an X.509 certificate.
   */
  kCertX509Asn1SerialNumberSizeInBytes = 20,

  /**
   * Cert key ID size (used for the serial number and auth key ID fields).
   */
  kCertKeyIdSizeInBytes = kCertX509Asn1SerialNumberSizeInBytes,
};

enum dice_x509_cert_expectations {
  /**
   * Size of the SerialNumber region header.
   * Expects 1B tag + 1B len + 1B 0x00
   */
  kDiceX509SerialHeaderSizeBytes = 3,

  /**
   * Total size in bytes of the SerialNumber region.
   * Expects header + 20B key id with MSb set.
   */
  kDiceX509SerialSizeBytes =
      kDiceX509SerialHeaderSizeBytes + kCertKeyIdSizeInBytes,

  /**
   * Offset to the SerialNumber region including header.
   * This offset is relative to the *begin* of signed cert.
   */
  kDiceX509SerialOffsetBytes = 13,

  /**
   * All valid X509 cert should be longer than this size.
   */
  kDiceX509MinSizeBytes = kDiceX509SerialOffsetBytes + kDiceX509SerialSizeBytes,
};

typedef uint8_t cert_key_id_t[kCertKeyIdSizeInBytes];

/**
 * DICE certificate format. It supports 2 types currently.
 * Each DICE implementation declares one of those specifically.
 */
typedef enum dice_cert_format {
  kDiceCertFormatX509TcbInfo = 0,
  kDiceCertFormatCWTAndroid = 1,
} dice_cert_format_t;

/**
 * Defines a grouping of certificates onto a single flash info page.
 */
typedef struct cert_flash_info_layout {
  /**
   * Boolean to indicate if this layout configuration is used by the
   * personalization firmware. This enables supporting personalization firmware
   * extensions.
   */
  bool used;
  /**
   * A name string for the group of certificates (e.g., "DICE").
   */
  char *group_name;
  /**
   * The flash info page a set of certificates will be written too.
   */
  const flash_ctrl_info_page_t *info_page;
  /**
   * The number of certificates that will be written to the flash info page.
   */
  size_t num_certs;

} cert_flash_info_layout_t;

/**
 * A set of public key IDs required to generate an X.509 certificate.
 */
typedef struct cert_key_id_pair {
  /**
   * Pointer to SHA256 digest of the public key matching the private key used to
   * endorse the certificate.
   */
  hmac_digest_t *endorsement;
  /**
   * Pointer to SHA256 digest of the public key the certificate is created for.
   */
  hmac_digest_t *cert;
} cert_key_id_pair_t;

/**
 * Decodes the ASN1 size header word to extract the number of bytes contained in
 * the ASN1 blob.
 *
 * @param header Buffer of four bytes that represents the ASN1 header.
 * @return Size (in bytes) of the ASN1 blob.
 */
uint32_t cert_x509_asn1_decode_size_header(const uint8_t *header);

/**
 * Check if the serial number field from an ASN.1 DER encoded X.509
 * certificate is expected.
 *
 * This function expects a certificate with a serial number encoded using the
 * MSb tweak. If the certificate does not have the MSb set for the serial int,
 * the function may return unmatched.
 *
 * @param cert Pointer to the buffer holding the certificate blob.
 * @param size Size of the `cert` buffer in bytes.
 * @param expected_sn_bytes Expected serial number bytes (in big endian order).
 * @param[out] matches True if expected serial number found. False otherwise.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t cert_x509_asn1_check_serial_number(const uint8_t *cert, size_t size,
                                               cert_key_id_t *expected_sn_bytes,
                                               hardened_bool_t *matches);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
