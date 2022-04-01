// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_rnd.h"

namespace mask_rom_test {
extern "C" uint32_t rnd_uint32(void) { return MockRnd::Instance().Uint32(); }
}  // namespace mask_rom_test
