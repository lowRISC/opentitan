// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/mock_sigverify_keys_ptrs.h"

namespace rom_test {
extern "C" {
const sigverify_rom_key_t *sigverify_rsa_keys_ptr_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysPtrGet();
}

size_t sigverify_num_rsa_keys_get() {
  return MockSigverifyKeysPtrs::Instance().NumRsaKeysGet();
}

size_t sigverify_rsa_keys_step_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysStepGet();
}
}  // extern "C"
}  // namespace rom_test
