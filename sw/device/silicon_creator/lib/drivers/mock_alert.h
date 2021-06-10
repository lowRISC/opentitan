// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_ALERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_ALERT_H_

#include "sw/device/lib/testing/mask_rom_test.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for alert.c.
 */
class MockAlert {
 public:
  MOCK_METHOD(rom_error_t, alert_configure,
              (size_t, alert_class_t, alert_enable_t));
  MOCK_METHOD(rom_error_t, alert_local_configure,
              (size_t, alert_class_t, alert_enable_t));
  MOCK_METHOD(rom_error_t, alert_class_configure,
              (alert_class_t, const alert_class_config_t *));
  MOCK_METHOD(rom_error_t, alert_ping_enable, ());
  virtual ~MockAlert() {}
};

}  // namespace internal

using MockAlert = GlobalMock<testing::StrictMock<internal::MockAlert>>;

extern "C" {

rom_error_t alert_configure(size_t index, alert_class_t cls,
                            alert_enable_t enabled) {
  return MockAlert::Instance().alert_configure(index, cls, enabled);
}

rom_error_t alert_local_configure(size_t index, alert_class_t cls,
                                  alert_enable_t enabled) {
  return MockAlert::Instance().alert_local_configure(index, cls, enabled);
}

rom_error_t alert_class_configure(alert_class_t cls,
                                  const alert_class_config_t *config) {
  return MockAlert::Instance().alert_class_configure(cls, config);
}

rom_error_t alert_ping_enable(void) {
  return MockAlert::Instance().alert_ping_enable();
}

}  // extern "C"
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_ALERT_H_
