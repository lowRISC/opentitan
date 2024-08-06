// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

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
   * Size of an X.509 ASN.1 DER encoded certificate up to, and including, the
   * serial number.
   *
   * Offset of ASN.1 tag is 13 plus:
   *  - 1 byte of tag
   *  - 1 byte of size
   *  - (potentially) 1 byte of padding
   *  - 20 bytes of serial number
   */
  kCertX509Asn1FirstBytesWithSerialNumber =
      kCertX509Asn1SerialNumberFieldByteOffset +
      kCertX509Asn1SerialNumberSizeInBytes + 3,
};

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
  /**
   * A array of name strings, one for each certificate in the group.
   */
  char **names;
} cert_flash_info_layout_t;

/**
 * Generates an ECC P256 keypair to build a certificate around, using Keymgr
 * and OTBN, returning the public key and a key ID (which is a SHA256 digest of
 * the public key).
 *
 * Preconditions: keymgr has been initialized and cranked to the desired stage.
 *
 * @param key The description of the desired key to generate.
 * @param[out] pubkey_id The public key ID (for embedding into certificates).
 * @param[out] pubkey The public key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t cert_ecc_p256_keygen(sc_keymgr_ecc_key_t key,
                                 hmac_digest_t *pubkey_id,
                                 ecdsa_p256_public_key_t *pubkey);

/**
 * Decodes the ASN1 size header word to extract the number of bytes contained in
 * the ASN1 blob.
 *
 * @param header Buffer of four bytes that represents the ASN1 header.
 * @return Size (in bytes) of the ASN1 blob.
 */
uint32_t cert_x509_asn1_decode_size_header(const uint8_t *header);

/**
 * Reads the first word of the certificate, which contains it's size, decodes
 * it, and returns the size of the certificate in bytes.
 *
 * @param info_page Pointer to the flash info page the certificate is on.
 * @param offset Byte offset on the flash info page the certificate starts at.
 * @param[out] size The size of the certificate in bytes (including the header).
 * @return Result of the operation.
 */
rom_error_t cert_x509_asn1_get_size_in_bytes(
    const flash_ctrl_info_page_t *info_page, uint32_t offset, uint32_t *size);

/**
 * Extracts the serial number field from an ASN.1 DER encoded X.509
 * certificate and checks if it matches what is expected.
 *
 * @param cert_page_buffer Pointer to the buffer holding the certificate blob.
 * @param offset Byte offset into the certificate buffer to start reading at.
 * @param expected_sn_bytes Expected serial number bytes (in big endian order).
 * @param[out] matches True if expected serial number found. False otherwise.
 * @param[out] out_cert_size The certificate size in bytes. Can be NULL if
 *                           caller does not want it returned.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t cert_x509_asn1_check_serial_number(const uint8_t *cert_page_buffer,
                                               size_t offset,
                                               uint8_t *expected_sn_bytes,
                                               hardened_bool_t *matches,
                                               uint32_t *out_cert_size);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CERT_H_
