// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "pinmux_regs.h"  // Generated.

namespace pinmux_unittest {
namespace {
class PinmuxTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_PINMUX_AON_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
};

class InitTest : public PinmuxTest {
 protected:
  /**
   * Set to track which peripheral inputs have already been configured.
   */
  std::set<top_earlgrey_pinmux_peripheral_in_t> configured_in_;

  /**
   * Register the configuration of the input peripheral in the tracking
   * set and return its computed address.
   *
   * Triggers a test failure if the input has already been registered.
   */
  uint32_t RegIn(top_earlgrey_pinmux_peripheral_in_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxPeripheralInLast);
    EXPECT_TRUE(configured_in_.insert(index).second);
    return base_ + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  }

  /**
   * Set to track which MIO outputs have already been configured.
   */
  std::set<top_earlgrey_pinmux_mio_out_t> configured_out_;

  /**
   * Register the configuration of the MIO output in the tracking
   * set and return its computed address.
   *
   * Triggers a test failure if the input has already been registered.
   */
  uint32_t RegOut(top_earlgrey_pinmux_mio_out_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxMioOutLast);
    EXPECT_TRUE(configured_out_.insert(index).second);
    return base_ + PINMUX_MIO_OUTSEL_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  };
};

TEST_F(InitTest, Initialize) {
  // The inputs that will be configured.
  EXPECT_ABS_WRITE32(RegIn(kTopEarlgreyPinmuxPeripheralInGpioGpio17),
                     kTopEarlgreyPinmuxInselIob8)
  EXPECT_ABS_WRITE32(RegIn(kTopEarlgreyPinmuxPeripheralInUart0Rx),
                     kTopEarlgreyPinmuxInselIoc3);

  // The outputs that will be configured.
  EXPECT_ABS_WRITE32(RegOut(kTopEarlgreyPinmuxMioOutIoc4),
                     kTopEarlgreyPinmuxOutselUart0Tx);

  pinmux_init();
}

}  // namespace
}  // namespace pinmux_unittest
