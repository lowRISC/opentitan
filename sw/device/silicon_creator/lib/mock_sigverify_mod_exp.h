// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SIGVERIFY_MOD_EXP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SIGVERIFY_MOD_EXP_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/sigverify_mod_exp.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for sigverify_mod_exp.h
 */
class MockSigverifyModExp {
 public:
  MOCK_METHOD(rom_error_t, ibex,
              (const sigverify_rsa_key_t *, const sigverify_rsa_buffer_t *,
               sigverify_rsa_buffer_t *));
  virtual ~MockSigverifyModExp() {}
};

}  // namespace internal

using MockSigverifyModExp =
    GlobalMock<testing::StrictMock<internal::MockSigverifyModExp>>;

extern "C" {

rom_error_t sigverify_mod_exp_ibex(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  return MockSigverifyModExp::Instance().ibex(key, sig, result);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SIGVERIFY_MOD_EXP_H_
