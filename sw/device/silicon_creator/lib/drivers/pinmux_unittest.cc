// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/pinmux.h"

#include "dt/dt_api.h"
#include "dt/dt_gpio.h"
#include "dt/dt_pinmux.h"
#include "dt/dt_uart.h"
#include "gtest/gtest.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/mock_csr.h"
#include "sw/device/silicon_creator/lib/drivers/mock_otp.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top/otp_ctrl_regs.h"
#include "hw/top/pinmux_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

namespace pinmux_unittest {
namespace {
using ::testing::Return;

class PinmuxTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_EARLGREY_PINMUX_AON_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
  rom_test::MockOtp otp_;
  mock_csr::MockCsr csr_;
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

  uint32_t RegInSelRegwen(top_earlgrey_pinmux_peripheral_in_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxPeripheralInLast);
    return base_ + PINMUX_MIO_PERIPH_INSEL_REGWEN_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  }

  uint32_t RegPadAttrRegwen(top_earlgrey_muxed_pads_t pad) {
    return base_ + PINMUX_MIO_PAD_ATTR_REGWEN_0_REG_OFFSET +
           static_cast<uint32_t>(pad) * sizeof(uint32_t);
  }

  uint32_t RegPadAttr(top_earlgrey_muxed_pads_t pad) {
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

  uint32_t RegOutSelRegwen(top_earlgrey_pinmux_mio_out_t index) {
    EXPECT_TRUE(index >= 0 && index < kTopEarlgreyPinmuxMioOutLast);
    return base_ + PINMUX_MIO_OUTSEL_REGWEN_0_REG_OFFSET +
           static_cast<uint32_t>(index) * sizeof(uint32_t);
  };
};

TEST_F(InitTest, PadAttrPropagationDelay) {
  const uint64_t kCpuClockPeriodNs = 1'000'000'000 / kClockFreqCpuHz;
  const uint64_t kCpuCyclesIn5Micros = 5000 / kCpuClockPeriodNs;
  EXPECT_EQ(PINMUX_PAD_ATTR_PROP_CYCLES, kCpuCyclesIn5Micros);
}

TEST_F(InitTest, EnablePullDownLocked) {
  EXPECT_ABS_READ32(RegPadAttrRegwen(kTopEarlgreyMuxedPadsIoc0),
                    {{PINMUX_MIO_PAD_ATTR_REGWEN_0_EN_0_BIT, 0}});

  EXPECT_EQ(pinmux_enable_pull_down(kDtPadIoc0), kErrorPinMuxLockedPad);
}

TEST_F(InitTest, EnablePullDown) {
  EXPECT_ABS_READ32(RegPadAttrRegwen(kTopEarlgreyMuxedPadsIoc0),
                    {{PINMUX_MIO_PAD_ATTR_REGWEN_0_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegPadAttr(kTopEarlgreyMuxedPadsIoc0),
                     {{PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, 1},
                      {PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT, 0}});
  EXPECT_CSR_WRITE(CSR_REG_MCYCLE, 0);
  for (size_t i = 0; i < 6; ++i) {
    EXPECT_CSR_READ(CSR_REG_MCYCLE, i * 100);
  }

  EXPECT_EQ(pinmux_enable_pull_down(kDtPadIoc0), kErrorOk);
}

TEST_F(InitTest, EnablePullUp) {
  EXPECT_ABS_READ32(RegPadAttrRegwen(kTopEarlgreyMuxedPadsIoc0),
                    {
                        {PINMUX_MIO_PAD_ATTR_REGWEN_0_EN_0_BIT, 1},
                    });
  EXPECT_ABS_WRITE32(RegPadAttr(kTopEarlgreyMuxedPadsIoc0),
                     {{PINMUX_MIO_PAD_ATTR_0_PULL_EN_0_BIT, 1},
                      {PINMUX_MIO_PAD_ATTR_0_PULL_SELECT_0_BIT, 1}});
  EXPECT_CSR_WRITE(CSR_REG_MCYCLE, 0);
  for (size_t i = 0; i < 6; ++i) {
    EXPECT_CSR_READ(CSR_REG_MCYCLE, i * 100);
  }

  EXPECT_EQ(pinmux_enable_pull_up(kDtPadIoc0), kErrorOk);
}

TEST_F(InitTest, ConnectMioIn) {
  EXPECT_ABS_READ32(RegInSelRegwen(kTopEarlgreyPinmuxPeripheralInGpioGpio22),
                    {{PINMUX_MIO_PERIPH_INSEL_REGWEN_0_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegInSel(kTopEarlgreyPinmuxPeripheralInGpioGpio22),
                     kTopEarlgreyPinmuxInselIoc0)

  EXPECT_ABS_READ32(RegOutSelRegwen(kTopEarlgreyPinmuxMioOutIoc0),
                    {{PINMUX_MIO_OUTSEL_REGWEN_0_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegOutSel(kTopEarlgreyPinmuxMioOutIoc0),
                     kDtPinmuxOutselConstantHighZ);

  EXPECT_EQ(pinmux_connect(dt_gpio_periph_io(kDtGpio, kDtGpioPeriphIoGpio22),
                           kDtPadIoc0, kDtPeriphIoDirIn),
            kErrorOk);
}

TEST_F(InitTest, ConnectMioIoOut) {
  EXPECT_ABS_READ32(RegOutSelRegwen(kTopEarlgreyPinmuxMioOutIoc4),
                    {{PINMUX_MIO_OUTSEL_REGWEN_0_EN_0_BIT, 1}});
  EXPECT_ABS_WRITE32(RegOutSel(kTopEarlgreyPinmuxMioOutIoc4),
                     kTopEarlgreyPinmuxOutselUart0Tx);

  EXPECT_EQ(pinmux_connect(dt_uart_periph_io(kDtUart0, kDtUartPeriphIoTx),
                           kDtPadIoc4, kDtPeriphIoDirOut),
            kErrorOk);
}

}  // namespace
}  // namespace pinmux_unittest
