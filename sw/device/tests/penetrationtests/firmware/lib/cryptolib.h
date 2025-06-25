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

// Arbitrary mask for testing (borrowed from aes_functest.c).
static const uint32_t kAesKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0x8bf85383, 0x05ab50b4,
    0x8acdcb7e, 0x15e76440, 0x8459b2ce, 0xdc2110cc,
};

static const uint32_t kHmacMask[48] = {
    0xBA81767F, 0xA913C751, 0x34209992, 0x5F66021B, 0x775F4577, 0x7C02E1CE,
    0xB4A8B698, 0x1986B902, 0x7251045B, 0x3C827C6F, 0x00909D12, 0x81ABC8F9,
    0x62F2FCB6, 0x15B63124, 0x66F60052, 0xAD637669, 0x522779CF, 0x07E9FBA8,
    0x1258E541, 0x860719EF, 0x1D4F5386, 0xA9B04F7C, 0x6E98A861, 0xEFADEBA6,
    0x900E1EC8, 0xB290DBCE, 0x05946814, 0xB83A01CE, 0x4EEC86BD, 0xAE836C6C,
    0x20182AAE, 0x4476F6F4, 0x7C4A0A31, 0x7D2809BA, 0x367B29B9, 0x42444BEA,
    0xDFD6025C, 0x1E665207, 0x18E0895B, 0x20D435DB, 0xC509A6D6, 0x8CC19AB1,
    0xA5D39BD2, 0xAB479AD5, 0x5786D029, 0x2E4B7CD7, 0xB77A3D76, 0xE2A09962,
};

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_H_
