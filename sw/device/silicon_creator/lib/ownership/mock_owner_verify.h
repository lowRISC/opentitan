// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNER_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNER_VERIFY_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for owner_verify.c.
 */
class MockOwnerVerify : public global_mock::GlobalMock<MockOwnerVerify> {
 public:
  MOCK_METHOD(rom_error_t, verify,
              (uint32_t, const owner_keydata_t *,
               const ecdsa_p256_signature_t *,
               const sigverify_spx_signature_t *, const void *, size_t,
               const void *, size_t, const void *, size_t,
               const hmac_digest_t *, uint32_t *));
};

}  // namespace internal

using MockOwnerVerify = testing::StrictMock<internal::MockOwnerVerify>;
using NiceMockOwnerVerify = testing::NiceMock<internal::MockOwnerVerify>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_MOCK_OWNER_VERIFY_H_
