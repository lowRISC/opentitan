// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/mock_boot_data.h"

namespace rom_test {
extern "C" {
rom_error_t boot_data_read(lifecycle_state_t lc_state, boot_data_t *boot_data) {
  return MockBootData::Instance().Read(lc_state, boot_data);
}

rom_error_t boot_data_write(const boot_data_t *boot_data) {
  return MockBootData::Instance().Write(boot_data);
}

rom_error_t boot_data_digest_is_valid(const boot_data *boot_data) {
  return MockBootData::Instance().Check(boot_data);
}
}  // extern "C"
}  // namespace rom_test
