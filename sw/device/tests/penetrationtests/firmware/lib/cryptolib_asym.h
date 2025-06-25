// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_ASYM_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_ASYM_H_

enum {
  /**
   * Number of words and bytes for different RSA modes.
   */
  kPentestRsa2048NumBytes = 2048 / 8,
  kPentestRsa2048NumWords = kPentestRsa2048NumBytes / sizeof(uint32_t),
  kPentestRsa3072NumBytes = 3072 / 8,
  kPentestRsa3072NumWords = kPentestRsa2048NumBytes / sizeof(uint32_t),
  kPentestRsa4096NumBytes = 4096 / 8,
  kPentestRsa4096NumWords = kPentestRsa4096NumBytes / sizeof(uint32_t),
  /**
   * RSA mode definitions.
   */
  kPentestRsa2048 = 0,
  kPentestRsa3072 = 1,
  kPentestRsa4096 = 2,
  /**
   * RSA hash mode definitions.
   */
  kPentestRsaHashmodeSha256 = 0,
  kPentestRsaHashmodeSha384 = 1,
  kPentestRsaHashmodeSha512 = 2,
  /**
   * Number of max words in a RSA msg.
   */
  kPentestRsaMaxMsgWords = RSA_CMD_MAX_MESSAGE_BYTES / sizeof(uint32_t),
  /**
   * Number of max N words in RSA.
   */
  kPentestRsaMaxNWords = RSA_CMD_MAX_N_BYTES / sizeof(uint32_t),
  /**
   * Number of max D words in RSA.
   */
  kPentestRsaMaxDWords = RSA_CMD_MAX_N_BYTES / sizeof(uint32_t),
};

#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_FIRMWARE_LIB_CRYPTOLIB_ASYM_H_
