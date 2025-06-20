// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_H_

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
   * Number of words in a key.
   */
  kPentestAesMaxKeyWords = AES_CMD_MAX_KEY_BYTES / sizeof(uint32_t),
};

// Arbitrary mask for testing (borrowed from aes_functest.c).
static const uint32_t kAesKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_H_
