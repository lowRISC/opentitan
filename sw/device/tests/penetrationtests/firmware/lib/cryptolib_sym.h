// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_SYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_SYM_H_

enum {
  /**
   * AES mode definitions.
   */
  kPentestAesModeEcb = 0,
  kPentestAesModeCbc = 1,
  kPentestAesModeCfb = 2,
  kPentestAesModeOfb = 3,
  kPentestAesModeCtr = 4,
  /**
   * AES mode definitions.
   */
  kPentestAesPaddingNull = 0,
  kPentestAesPaddingPkcs7 = 1,
  kPentestAesPaddingIso9797M2 = 2,
  /**
   * Fixed AES IV size.
   */
  kPentestAesIvSize = 4,
  /**
   * Number of words in a block.
   */
  kPentestAesBlockWords = AES_CMD_MAX_BLOCK_BYTES / sizeof(uint32_t),
  /**
   * Number of words in an AES key.
   */
  kPentestAesMaxKeyWords = AES_CMD_MAX_KEY_BYTES / sizeof(uint32_t),
  /**
   * Number of words in a HMAC key.
   */
  kPentestHmacMaxKeyWords = HMAC_CMD_MAX_KEY_BYTES / sizeof(uint32_t),
  /**
   * HMAC mode definitions.
   */
  kPentestHmacHashAlgSha256 = 0,
  kPentestHmacHashAlgSha384 = 1,
  kPentestHmacHashAlgSha512 = 2,
  /**
   * HMAC number of tag bytes for each mode.
   */
  kPentestHmacTagBytesSha256 = 32,
  kPentestHmacTagBytesSha384 = 48,
  kPentestHmacTagBytesSha512 = 64,
  /**
   * Number of max words in a tag.
   */
  kPentestHmacMaxTagWords = HMAC_CMD_MAX_TAG_BYTES / sizeof(uint32_t),
};

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_SYM_H_
