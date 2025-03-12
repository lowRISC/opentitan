// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/cert.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/error.h"

static_assert(kCertX509Asn1SerialNumberSizeInBytes <= kHmacDigestNumBytes,
              "The ASN.1 encoded X.509 serial number field should be <= the "
              "size of a SHA256 digest.");

uint32_t cert_x509_asn1_decode_size_header(const uint8_t *header) {
  if (header[0] != 0x30 || header[1] != 0x82) {
    return 0;
  }
  return (((uint32_t)header[2]) << 8) + header[3] + 4 /* size of the header */;
}

rom_error_t cert_x509_asn1_check_serial_number(const uint8_t *cert, size_t size,
                                               cert_key_id_t *expected_sn_bytes,
                                               hardened_bool_t *matches) {
  *matches = kHardenedBoolFalse;
  if (size < kDiceX509MinSizeBytes) {
    return kErrorCertInvalidSize;
  }

  // We want the initializer for this to be `{0x02, 0x15, 0x00, ...}`, however
  // that results in 23 bytes of .rodata, 20 of which we immediately overwrite
  // by the memcpy below.  Initialization with code results in 16 bytes of
  // rv32imc code.
  char expected_serial[kDiceX509SerialSizeBytes];
  expected_serial[0] = 0x02;
  expected_serial[1] = 0x15;
  expected_serial[2] = 0x00;

  // Prepare expected serial number.
  memcpy(&expected_serial[kDiceX509SerialHeaderSizeBytes], expected_sn_bytes,
         kCertKeyIdSizeInBytes);
  expected_serial[kDiceX509SerialHeaderSizeBytes] |= 0x80;  // Tweak MSb.

  // Check if serial number matches.
  const uint8_t *serial = cert + kDiceX509SerialOffsetBytes;
  if (memcmp(serial, expected_serial, sizeof(expected_serial)) == 0) {
    *matches = kHardenedBoolTrue;
  }

  return kErrorOk;
}
