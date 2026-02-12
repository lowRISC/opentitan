// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_clkmgr.h"

/**
 * Type of IP block to be tested; transactions to block(s) of the given
 * type will be attempted whilst its hintable clock is off.
 *
 * Transactions to IP block(s) of the other types are also attempted to
 * check that they remain functional throughout.
 */
typedef enum test_trans_block {
  kTestTransFirst = 0u,
  // List of types of IP block with hintable clocks.
  kTestTransAes = kTestTransFirst,
  kTestTransHmac,
  kTestTransKmac,
  kTestTransOtbn,
  // Number of types of IP block.
  kTestTransCount
} test_trans_block_t;

bool execute_off_trans_test(test_trans_block_t block);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_
