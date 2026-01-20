// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_retention_sram.h"

namespace rom_test {
extern "C" {

retention_sram_t *retention_sram_get(void) {
  return MockRetentionSram::Instance().Get();
}

}  // extern "C"
}  // namespace rom_test
