// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/cryptolib_build_info.h"

#include "sw/device/lib/crypto/drivers/cryptolib_build_info.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'b', 'i')

otcrypto_status_t otcrypto_build_info(uint32_t *version, bool *released,
                                      uint32_t *build_hash_low,
                                      uint32_t *build_hash_high) {
  *version = kCryptoLibBuildInfo.version;
  *released = kCryptoLibBuildInfo.released;
  *build_hash_low = kCryptoLibBuildInfo.scm_revision.scm_revision_low;
  *build_hash_high = kCryptoLibBuildInfo.scm_revision.scm_revision_high;

  return LAUNDERED_OTCRYPTO_OK;
}

otcrypto_lib_version_t otcrypto_lib_version(void) {
  return (otcrypto_lib_version_t)kCryptoLibVersion;
}

void otcrypto_version_decode(uint32_t version, uint32_t *major, uint32_t *minor,
                             uint32_t *patch) {
  // Uses modular multiplicative inverse mod 2^32 for decoding
  uint32_t decoded = version * 0x332ce355u;
  *major = (decoded >> 24) & 0xff;
  *minor = (decoded >> 16) & 0xff;
  *patch = (decoded >> 8) & 0xff;
}
