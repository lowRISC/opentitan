// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_alert.h"

namespace rom_test {
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
}  // namespace rom_test
