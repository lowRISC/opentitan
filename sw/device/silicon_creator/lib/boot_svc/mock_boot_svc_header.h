// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_MOCK_BOOT_SVC_HEADER_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_MOCK_BOOT_SVC_HEADER_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for boot_svc_header.c.
 */
class MockBootSvcHeader : public global_mock::GlobalMock<MockBootSvcHeader> {
 public:
  MOCK_METHOD(void, Finalize, (uint32_t, uint32_t, boot_svc_header_t *));
};

}  // namespace internal

using MockBootSvcHeader = testing::StrictMock<internal::MockBootSvcHeader>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_MOCK_BOOT_SVC_HEADER_H_
