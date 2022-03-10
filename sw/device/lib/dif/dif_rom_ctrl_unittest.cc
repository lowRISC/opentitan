// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rom_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "rom_ctrl_regs.h"  // Generated.
}  // extern "C"

namespace dif_rom_ctrl_test {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// TODO: Add unit tests.

}  // namespace
}  // namespace dif_rom_ctrl_test
