// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SHUTDOWN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SHUTDOWN_H_

#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for shutdown.
 */
class MockShutdown : public global_mock::GlobalMock<MockShutdown> {
 public:
  MOCK_METHOD(shutdown_error_redact_t, RedactPolicy, ());
  MOCK_METHOD(uint32_t, Redact, (rom_error_t, shutdown_error_redact_t));
  MOCK_METHOD(void, Finalize, (rom_error_t));
};

}  // namespace internal

using MockShutdown = testing::StrictMock<internal::MockShutdown>;

extern "C" {

shutdown_error_redact_t shutdown_redact_policy(void) {
  return MockShutdown::Instance().RedactPolicy();
}

uint32_t shutdown_redact(rom_error_t reason, shutdown_error_redact_t severity) {
  return MockShutdown::Instance().Redact(reason, severity);
}

void shutdown_finalize(rom_error_t reason) {
  return MockShutdown::Instance().Finalize(reason);
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MOCK_SHUTDOWN_H_
