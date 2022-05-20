// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/mask_rom_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"

namespace pinmux_unittest {
namespace {
using ::testing::Return;

class PinmuxTest : public mask_rom_test::MaskRomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_PINMUX_AON_BASE_ADDR;
  mask_rom_test::MockAbsMmio mmio_;
  mask_rom_test::MockOtp otp_;
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
  uint32_t RegInSel(top_earlgrey_pinmux_peripheral_in_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxPeripheralInLast);
    EXPECT_TRUE(configured_in_.insert(index).second);
    return base_ + PINMUX_MIO_PERIPH_INSEL_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  }

  uint32_t RegPadAttr(top_earlgrey_pinmux_insel_t pad) {
    return base_ + PINMUX_MIO_PAD_ATTR_0_REG_OFFSET +
           static_cast<uint32_t>(pad) * sizeof(uint32_t);
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
  uint32_t RegOutSel(top_earlgrey_pinmux_mio_out_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxMioOutLast);
    EXPECT_TRUE(configured_out_.insert(index).second);
    return base_ + PINMUX_MIO_OUTSEL_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  };
};

TEST_F(InitTest, WithBootstrap) {
  // The inputs that will be configured.
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_ROM_BOOTSTRAP_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolTrue));
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInGpioGpio22),
                     kTopEarlgreyPinmuxInselIoc0)
  EXPECT_ABS_WRITE32(RegPadAttr(kTopEarlgreyPinmuxInselIoc0),
                     {{PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInGpioGpio23),
                     kTopEarlgreyPinmuxInselIoc1)
  EXPECT_ABS_WRITE32(RegPadAttr(kTopEarlgreyPinmuxInselIoc1),
                     {{PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInGpioGpio24),
                     kTopEarlgreyPinmuxInselIoc2)
  EXPECT_ABS_WRITE32(RegPadAttr(kTopEarlgreyPinmuxInselIoc2),
                     {{PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInUart0Rx),
                     kTopEarlgreyPinmuxInselIoc3);

  // The outputs that will be configured.
  EXPECT_ABS_WRITE32(RegOutSel(kTopEarlgreyPinmuxMioOutIoc4),
                     kTopEarlgreyPinmuxOutselUart0Tx);

  pinmux_init();
}

TEST_F(InitTest, WithoutBootstrap) {
  // The inputs that will be configured.
  EXPECT_CALL(otp_, read32(OTP_CTRL_PARAM_ROM_BOOTSTRAP_EN_OFFSET))
      .WillOnce(Return(kHardenedBoolFalse));
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInUart0Rx),
                     kTopEarlgreyPinmuxInselIoc3);

  // The outputs that will be configured.
  EXPECT_ABS_WRITE32(RegOutSel(kTopEarlgreyPinmuxMioOutIoc4),
                     kTopEarlgreyPinmuxOutselUart0Tx);

  pinmux_init();
}

}  // namespace
}  // namespace pinmux_unittest
