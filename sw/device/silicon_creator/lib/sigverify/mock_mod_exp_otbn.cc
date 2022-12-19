// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/mock_mod_exp_otbn.h"

namespace rom_test {
extern "C" {
rom_error_t sigverify_mod_exp_otbn(const sigverify_rsa_key_t *key,
                                   const sigverify_rsa_buffer_t *sig,
                                   sigverify_rsa_buffer_t *result) {
  return MockSigverifyModExpOtbn::Instance().mod_exp(key, sig, result);
}
}  // extern "C"
}  // namespace rom_test
