// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_

#include "sw/device/silicon_creator/mask_rom/sigverify_keys_ptrs.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for sigverify_keys_ptrs.h
 */
class MockSigverifyKeysPtrs : public GlobalMock<MockSigverifyKeysPtrs> {
 public:
  MOCK_METHOD(const sigverify_mask_rom_key_t *, RsaKeysPtrGet, ());
  MOCK_METHOD(size_t, NumRsaKeysGet, ());
  MOCK_METHOD(size_t, RsaKeysStepGet, ());
};

}  // namespace internal

using MockSigverifyKeysPtrs =
    testing::StrictMock<internal::MockSigverifyKeysPtrs>;

extern "C" {

const sigverify_mask_rom_key_t *sigverify_rsa_keys_ptr_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysPtrGet();
}

size_t sigverify_num_rsa_keys_get() {
  return MockSigverifyKeysPtrs::Instance().NumRsaKeysGet();
}

size_t sigverify_rsa_keys_step_get() {
  return MockSigverifyKeysPtrs::Instance().RsaKeysStepGet();
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MASK_ROM_MOCK_SIGVERIFY_KEYS_PTRS_H_
