// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_IBEX_MOCK_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_IBEX_MOCK_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/sigverify/mod_exp_ibex.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for sigverify_mod_exp_ibex.c
 */
class MockSigverifyModExpIbex
    : public global_mock::GlobalMock<MockSigverifyModExpIbex> {
 public:
  MOCK_METHOD(rom_error_t, mod_exp,
              (const sigverify_rsa_key_t *, const sigverify_rsa_buffer_t *,
               sigverify_rsa_buffer_t *));
};

}  // namespace internal

using MockSigverifyModExpIbex =
    testing::StrictMock<internal::MockSigverifyModExpIbex>;
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_MOD_EXP_IBEX_MOCK_H_
