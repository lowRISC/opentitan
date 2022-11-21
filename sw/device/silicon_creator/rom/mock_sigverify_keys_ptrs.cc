// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/mock_sigverify_keys_ptrs.h"

namespace rom_test {
extern "C" {
const sigverify_rom_key_t *sigverify_rsa_keys_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysGet();
}

size_t sigverify_rsa_keys_cnt_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysCntGet();
}

}  // extern "C"
}  // namespace rom_test
