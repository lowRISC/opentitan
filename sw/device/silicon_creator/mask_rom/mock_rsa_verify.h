// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_RSA_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_RSA_VERIFY_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/mask_rom/rsa_verify.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for rsa_verify.c.
 */
class MockRsaVerify {
 public:
  MOCK_METHOD(bool, mod_exp_ibex,
              (const sigverify_rsa_key_t *, const sigverify_rsa_buffer_t *,
               sigverify_rsa_buffer_t *));
  virtual ~MockRsaVerify() {}
};

}  // namespace internal

using MockRsaVerify = GlobalMock<testing::StrictMock<internal::MockRsaVerify>>;

extern "C" {

bool sigverify_mod_exp_ibex(const sigverify_rsa_key_t *key,
                            const sigverify_rsa_buffer_t *sig,
                            sigverify_rsa_buffer_t *result) {
  return MockRsaVerify::Instance().mod_exp_ibex(key, sig, result);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_RSA_VERIFY_H_
