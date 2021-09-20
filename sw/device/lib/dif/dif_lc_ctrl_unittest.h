// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_UNITTEST_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_UNITTEST_H_

#include <cstring>
#include <limits>
#include <utility>

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"

#include "lc_ctrl_regs.h"  // Generated.

namespace dif_lc_ctrl_unittest {
namespace {
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;
using ::testing::Test;

class LcCtrlTest : public Test, public MmioTest {
 protected:
  dif_lc_ctrl_t lc_ = {.base_addr = dev().region()};
};

}  // namespace
}  // namespace dif_lc_ctrl_unittest

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_UNITTEST_H_
