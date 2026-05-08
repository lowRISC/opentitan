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

  return OTCRYPTO_OK;
}
