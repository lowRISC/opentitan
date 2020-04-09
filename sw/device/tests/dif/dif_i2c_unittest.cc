// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstring>
#include <limits>
#include <ostream>

extern "C" {
#include "sw/device/lib/dif/dif_i2c.h"
#include "i2c_regs.h"  // Generated.
}  // extern "C"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

// We define global namespace == and << to make `dif_i2c_timing_params_t` work
// nicely with EXPECT_EQ.
bool operator==(dif_i2c_timing_params_t a, dif_i2c_timing_params_t b) {
  // We just do a dumb memcmp. The timing params struct is essentially an array
  // of half-words, so we won't run into padding issues.
  return std::memcmp(&a, &b, sizeof(dif_i2c_timing_params_t)) == 0;
}

std::ostream &operator<<(std::ostream &os,
                         const dif_i2c_timing_params_t &params) {
  return os << "{\n"
            << "  .scl_time_high = " << params.scl_time_high << ",\n"
            << "  .scl_time_low = " << params.scl_time_low << ",\n"
            << "  .rise_time = " << params.rise_time << ",\n"
            << "  .fall_time = " << params.fall_time << ",\n"
            << "  .start_signal_setup_time = " << params.start_signal_setup_time
            << ",\n"
            << "  .start_signal_hold_time = " << params.start_signal_hold_time
            << ",\n"
            << "  .data_signal_setup_time = " << params.data_signal_setup_time
            << ",\n"
            << "  .data_signal_hold_time = " << params.data_signal_hold_time
            << ",\n"
            << "  .stop_signal_setup_time = " << params.stop_signal_setup_time
            << ",\n"
            << "  .stop_signal_hold_time = " << params.stop_signal_hold_time
            << ",\n"
            << "}";
}

namespace dif_i2c_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

// "Base" configs consisting of harware timings, in "slow" and "fast" variants.
constexpr dif_i2c_timing_config_t kBaseConfigSlow = {
    .lowest_target_device_speed =
        kDifI2cSpeedStandard,  // Remove once we upgrade the host compiler.
    .clock_period_nanos = 90,
    .sda_rise_nanos = 250,
    .sda_fall_nanos = 220,
};

constexpr dif_i2c_timing_config_t kBaseConfigFast = {
    .lowest_target_device_speed =
        kDifI2cSpeedStandard,  // Remove once we upgrade the host compiler.
    .clock_period_nanos = 20,
    .sda_rise_nanos = 120,
    .sda_fall_nanos = 130,
};

TEST(ComputeTimingTest, StandardSpeed) {
  dif_i2c_timing_config_t config;
  dif_i2c_timing_params_t params, expected;

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  expected = {
      .scl_time_high = 53,
      .scl_time_low = 53,
      .rise_time = 3,
      .fall_time = 3,
      .start_signal_setup_time = 53,
      .start_signal_hold_time = 45,
      .data_signal_setup_time = 3,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 45,
      .stop_signal_hold_time = 53,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  expected = {
      .scl_time_high = 252,
      .scl_time_low = 235,
      .rise_time = 6,
      .fall_time = 7,
      .start_signal_setup_time = 235,
      .start_signal_hold_time = 200,
      .data_signal_setup_time = 13,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 200,
      .stop_signal_hold_time = 235,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  config.scl_period_nanos = 11000;
  expected = {
      .scl_time_high = 64,
      .scl_time_low = 53,
      .rise_time = 3,
      .fall_time = 3,
      .start_signal_setup_time = 53,
      .start_signal_hold_time = 45,
      .data_signal_setup_time = 3,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 45,
      .stop_signal_hold_time = 53,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, FastSpeed) {
  dif_i2c_timing_config_t config;
  dif_i2c_timing_params_t params, expected;

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  expected = {
      .scl_time_high = 7,
      .scl_time_low = 15,
      .rise_time = 3,
      .fall_time = 3,
      .start_signal_setup_time = 7,
      .start_signal_hold_time = 7,
      .data_signal_setup_time = 2,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 7,
      .stop_signal_hold_time = 15,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  expected = {
      .scl_time_high = 47,
      .scl_time_low = 65,
      .rise_time = 6,
      .fall_time = 7,
      .start_signal_setup_time = 30,
      .start_signal_hold_time = 30,
      .data_signal_setup_time = 5,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 30,
      .stop_signal_hold_time = 65,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  config.scl_period_nanos = 8000;
  expected = {
      .scl_time_high = 68,
      .scl_time_low = 15,
      .rise_time = 3,
      .fall_time = 3,
      .start_signal_setup_time = 7,
      .start_signal_hold_time = 7,
      .data_signal_setup_time = 2,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 7,
      .stop_signal_hold_time = 15,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, FastPlusSpeed) {
  dif_i2c_timing_config_t config;
  dif_i2c_timing_params_t params, expected;

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFastPlus;
  expected = {
      .scl_time_high = 13,
      .scl_time_low = 25,
      .rise_time = 6,
      .fall_time = 7,
      .start_signal_setup_time = 13,
      .start_signal_hold_time = 13,
      .data_signal_setup_time = 3,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 13,
      .stop_signal_hold_time = 25,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFastPlus;
  config.scl_period_nanos = 1500;
  expected = {
      .scl_time_high = 37,
      .scl_time_low = 25,
      .rise_time = 6,
      .fall_time = 7,
      .start_signal_setup_time = 13,
      .start_signal_hold_time = 13,
      .data_signal_setup_time = 3,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 13,
      .stop_signal_hold_time = 25,
  };
  EXPECT_EQ(dif_i2c_compute_timing(&config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, NullArgs) {
  auto config = kBaseConfigFast;
  dif_i2c_timing_params_t params;
  EXPECT_EQ(dif_i2c_compute_timing(&config, nullptr), kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_compute_timing(nullptr, &params), kDifI2cBadArg);
}

class I2cTest : public testing::Test, public MmioTest {
 protected:
  dif_i2c_timing_params_t timing = {
      .scl_time_high = 252,
      .scl_time_low = 235,
      .rise_time = 6,
      .fall_time = 7,
      .start_signal_setup_time = 235,
      .start_signal_hold_time = 200,
      .data_signal_setup_time = 13,
      .data_signal_hold_time = 0,
      .stop_signal_setup_time = 200,
      .stop_signal_hold_time = 235,
  };

  dif_i2c_t i2c = {.base_addr = dev().region()};
};

class InitTest : public I2cTest {};

TEST_F(InitTest, NormalInit) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST, 0x1, 0x0}});

  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(I2C_INTR_ENABLE_REG_OFFSET, 0x0);

  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET, {{I2C_FIFO_CTRL_RXRST, 0x1, 0x1}});
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET, {{I2C_FIFO_CTRL_FMTRST, 0x1, 0x1}});

  EXPECT_MASK32(
      I2C_FIFO_CTRL_REG_OFFSET,
      {
          {
              I2C_FIFO_CTRL_RXILVL_OFFSET, I2C_FIFO_CTRL_RXILVL_MASK,
              I2C_FIFO_CTRL_RXILVL_RXLVL1,
          },
          {
              I2C_FIFO_CTRL_FMTILVL_OFFSET, I2C_FIFO_CTRL_FMTILVL_MASK,
              I2C_FIFO_CTRL_FMTILVL_FMTLVL1,
          },
      });

  EXPECT_WRITE32(I2C_TIMING0_REG_OFFSET,
                 {
                     {I2C_TIMING0_THIGH_OFFSET, timing.scl_time_high},
                     {I2C_TIMING0_TLOW_OFFSET, timing.scl_time_low},
                 });
  EXPECT_WRITE32(I2C_TIMING1_REG_OFFSET,
                 {
                     {I2C_TIMING1_T_R_OFFSET, timing.rise_time},
                     {I2C_TIMING1_T_F_OFFSET, timing.fall_time},
                 });
  EXPECT_WRITE32(
      I2C_TIMING2_REG_OFFSET,
      {
          {I2C_TIMING2_TSU_STA_OFFSET, timing.start_signal_setup_time},
          {I2C_TIMING2_THD_STA_OFFSET, timing.start_signal_hold_time},
      });
  EXPECT_WRITE32(
      I2C_TIMING3_REG_OFFSET,
      {
          {I2C_TIMING3_TSU_DAT_OFFSET, timing.data_signal_setup_time},
          {I2C_TIMING3_THD_DAT_OFFSET, timing.data_signal_hold_time},
      });
  EXPECT_WRITE32(
      I2C_TIMING4_REG_OFFSET,
      {
          {I2C_TIMING4_TSU_STO_OFFSET, timing.stop_signal_setup_time},
          {I2C_TIMING4_T_BUF_OFFSET, timing.stop_signal_hold_time},
      });

  EXPECT_EQ(dif_i2c_init(dev().region(), &timing, &i2c), kDifI2cOk);
}

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_i2c_init(dev().region(), &timing, nullptr), kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_init(dev().region(), nullptr, &i2c), kDifI2cBadArg);
}

class FifoCtrlTest : public I2cTest {};

TEST_F(FifoCtrlTest, RxReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET, {{I2C_FIFO_CTRL_RXRST, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_reset_rx_fifo(&i2c), kDifI2cOk);
}

TEST_F(FifoCtrlTest, RxNullArgs) {
  EXPECT_EQ(dif_i2c_reset_rx_fifo(nullptr), kDifI2cBadArg);
}

TEST_F(FifoCtrlTest, FmtReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET, {{I2C_FIFO_CTRL_FMTRST, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_reset_fmt_fifo(&i2c), kDifI2cOk);
}

TEST_F(FifoCtrlTest, FmtNullArgs) {
  EXPECT_EQ(dif_i2c_reset_fmt_fifo(nullptr), kDifI2cBadArg);
}

TEST_F(FifoCtrlTest, SetLevels) {
  EXPECT_MASK32(
      I2C_FIFO_CTRL_REG_OFFSET,
      {
          {
              I2C_FIFO_CTRL_RXILVL_OFFSET, I2C_FIFO_CTRL_RXILVL_MASK,
              I2C_FIFO_CTRL_RXILVL_RXLVL1,
          },
          {
              I2C_FIFO_CTRL_FMTILVL_OFFSET, I2C_FIFO_CTRL_FMTILVL_MASK,
              I2C_FIFO_CTRL_FMTILVL_FMTLVL1,
          },
      });
  EXPECT_EQ(dif_i2c_set_watermarks(&i2c, kDifI2cLevel1Byte, kDifI2cLevel1Byte),
            kDifI2cOk);

  EXPECT_MASK32(
      I2C_FIFO_CTRL_REG_OFFSET,
      {
          {
              I2C_FIFO_CTRL_RXILVL_OFFSET, I2C_FIFO_CTRL_RXILVL_MASK,
              I2C_FIFO_CTRL_RXILVL_RXLVL4,
          },
          {
              I2C_FIFO_CTRL_FMTILVL_OFFSET, I2C_FIFO_CTRL_FMTILVL_MASK,
              I2C_FIFO_CTRL_FMTILVL_FMTLVL16,
          },
      });
  EXPECT_EQ(dif_i2c_set_watermarks(&i2c, kDifI2cLevel4Byte, kDifI2cLevel16Byte),
            kDifI2cOk);

  EXPECT_MASK32(
      I2C_FIFO_CTRL_REG_OFFSET,
      {
          {
              I2C_FIFO_CTRL_RXILVL_OFFSET, I2C_FIFO_CTRL_RXILVL_MASK,
              I2C_FIFO_CTRL_RXILVL_RXLVL30,
          },
          {
              I2C_FIFO_CTRL_FMTILVL_OFFSET, I2C_FIFO_CTRL_FMTILVL_MASK,
              I2C_FIFO_CTRL_FMTILVL_FMTLVL8,
          },
      });
  EXPECT_EQ(dif_i2c_set_watermarks(&i2c, kDifI2cLevel30Byte, kDifI2cLevel8Byte),
            kDifI2cOk);

  EXPECT_EQ(
      dif_i2c_set_watermarks(&i2c, kDifI2cLevel30Byte, kDifI2cLevel30Byte),
      kDifI2cBadArg);
}

TEST_F(FifoCtrlTest, SetLevelsNullArgs) {
  EXPECT_EQ(
      dif_i2c_set_watermarks(nullptr, kDifI2cLevel4Byte, kDifI2cLevel16Byte),
      kDifI2cBadArg);
}

class IrqTest : public I2cTest {};

TEST_F(IrqTest, Get) {
  bool flag;

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_get(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow, &flag),
            kDifI2cOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK, 0x0}});
  EXPECT_EQ(dif_i2c_irq_get(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow, &flag),
            kDifI2cOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_get(&i2c, kDifI2cIrqTypeNak, &flag), kDifI2cOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK, 0x0}});
  EXPECT_EQ(dif_i2c_irq_get(&i2c, kDifI2cIrqTypeNak, &flag), kDifI2cOk);
  EXPECT_FALSE(flag);
}

TEST_F(IrqTest, GetNullArgs) {
  bool flag;

  EXPECT_EQ(dif_i2c_irq_get(nullptr, kDifI2cIrqTypeNak, &flag), kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_irq_get(&i2c, kDifI2cIrqTypeNak, nullptr), kDifI2cBadArg);
}

TEST_F(IrqTest, Clear) {
  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 {{I2C_INTR_STATE_FMT_WATERMARK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_clear(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_clear(&i2c, kDifI2cIrqTypeNak), kDifI2cOk);
}

TEST_F(IrqTest, ClearNullArgs) {
  EXPECT_EQ(dif_i2c_irq_clear(nullptr, kDifI2cIrqTypeNak), kDifI2cBadArg);
}

TEST_F(IrqTest, Enable) {
  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow,
                                    kDifI2cEnabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow,
                                    kDifI2cDisabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET, {{I2C_INTR_STATE_NAK, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTypeNak, kDifI2cEnabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET, {{I2C_INTR_STATE_NAK, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c, kDifI2cIrqTypeNak, kDifI2cDisabled),
            kDifI2cOk);
}

TEST_F(IrqTest, EnableNullArgs) {
  EXPECT_EQ(dif_i2c_irq_set_enabled(nullptr, kDifI2cIrqTypeNak, kDifI2cEnabled),
            kDifI2cBadArg);
}

TEST_F(IrqTest, Force) {
  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET,
                 {{I2C_INTR_TEST_FMT_WATERMARK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c, kDifI2cIrqTypeFmtWatermarkUnderflow),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET, {{I2C_INTR_TEST_NAK, 0x1}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c, kDifI2cIrqTypeNak), kDifI2cOk);
}

TEST_F(IrqTest, ForceNullArgs) {
  EXPECT_EQ(dif_i2c_irq_force(nullptr, kDifI2cIrqTypeNak), kDifI2cBadArg);
}

class ControlTest : public I2cTest {};

TEST_F(ControlTest, HostEnable) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_host_set_enabled(&i2c, kDifI2cEnabled), kDifI2cOk);

  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_host_set_enabled(&i2c, kDifI2cDisabled), kDifI2cOk);
}

TEST_F(ControlTest, HostEnableNullArgs) {
  EXPECT_EQ(dif_i2c_host_set_enabled(nullptr, kDifI2cEnabled), kDifI2cBadArg);
}

class OverrideTest : public I2cTest {};

TEST_F(OverrideTest, Enable) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_override_set_enabled(&i2c, kDifI2cEnabled), kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_override_set_enabled(&i2c, kDifI2cDisabled), kDifI2cOk);
}

TEST_F(OverrideTest, EnableNullArgs) {
  EXPECT_EQ(dif_i2c_override_set_enabled(nullptr, kDifI2cEnabled),
            kDifI2cBadArg);
}

TEST_F(OverrideTest, Drive) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET,
                {
                    {I2C_OVRD_SCLVAL, 0x1, 0x0}, {I2C_OVRD_SDAVAL, 0x1, 0x0},
                });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c, false, false), kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET,
                {
                    {I2C_OVRD_SCLVAL, 0x1, 0x0}, {I2C_OVRD_SDAVAL, 0x1, 0x1},
                });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c, false, true), kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET,
                {
                    {I2C_OVRD_SCLVAL, 0x1, 0x1}, {I2C_OVRD_SDAVAL, 0x1, 0x1},
                });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c, true, true), kDifI2cOk);
}

TEST_F(OverrideTest, DriveNullArgs) {
  EXPECT_EQ(dif_i2c_override_drive_pins(nullptr, false, false), kDifI2cBadArg);
}

TEST_F(OverrideTest, Sample) {
  uint16_t scl, sda;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c, &scl, &sda), kDifI2cOk);
  EXPECT_EQ(scl, 0x3847);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c, nullptr, &sda), kDifI2cOk);
  EXPECT_EQ(scl, 0x0);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c, &scl, nullptr), kDifI2cOk);
  EXPECT_EQ(scl, 0x3847);
  EXPECT_EQ(sda, 0x0);
}

TEST_F(OverrideTest, SampleNullArgs) {
  uint16_t scl, sda;
  EXPECT_EQ(dif_i2c_override_sample_pins(nullptr, &scl, &sda), kDifI2cBadArg);
}

class FifoTest : public I2cTest {};

TEST_F(FifoTest, GetLevels) {
  uint8_t rx, fmt;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c, &rx, &fmt), kDifI2cOk);
  EXPECT_EQ(rx, 0x7);
  EXPECT_EQ(fmt, 0x29);

  rx = 0, fmt = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c, nullptr, &fmt), kDifI2cOk);
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(fmt, 0x29);

  rx = 0, fmt = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c, &rx, nullptr), kDifI2cOk);
  EXPECT_EQ(rx, 0x7);
  EXPECT_EQ(fmt, 0x0);
}

TEST_F(FifoTest, GetLevelsNullArgs) {
  uint8_t rx, fmt;
  EXPECT_EQ(dif_i2c_get_fifo_levels(nullptr, &rx, &fmt), kDifI2cBadArg);
}

TEST_F(FifoTest, Read) {
  uint8_t val;

  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xab);
  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xcd);
  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xef);

  EXPECT_EQ(dif_i2c_read_byte(&i2c, &val), kDifI2cOk);
  EXPECT_EQ(val, 0xab);
  EXPECT_EQ(dif_i2c_read_byte(&i2c, &val), kDifI2cOk);
  EXPECT_EQ(val, 0xcd);
  EXPECT_EQ(dif_i2c_read_byte(&i2c, nullptr), kDifI2cOk);
  EXPECT_EQ(val, 0xcd);
}

TEST_F(FifoTest, ReadNullArgs) {
  uint8_t val;
  EXPECT_EQ(dif_i2c_read_byte(nullptr, &val), kDifI2cBadArg);
}

// NOTE: `false` settings on the below designated initializers are only
// for a workaround in GCC 5, and should be removed once the host toolchain is
// upgraded.

TEST_F(FifoTest, WriteRaw) {
  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET,
                 {
                     {I2C_FDATA_FBYTE_OFFSET, 0x44}, {I2C_FDATA_START, 0x1},
                 });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c, 0x44,
                                   {
                                       .start = true,
                                   }),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x55},
                                       });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c, 0x55, {}), kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x66},
                                           {I2C_FDATA_STOP, 0x1},
                                           {I2C_FDATA_NAKOK, 0x1},
                                       });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c, 0x66,
                                   {
                                       .start = false,
                                       .stop = true,
                                       .read = false,
                                       .read_cont = false,
                                       .supress_nak_irq = true,
                                   }),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x00},
                                           {I2C_FDATA_READ, 0x1},
                                           {I2C_FDATA_RCONT, 0x1},
                                       });
  EXPECT_EQ(
      dif_i2c_write_byte_raw(
          &i2c, 0x00,
          {
              .start = false, .stop = false, .read = true, .read_cont = true,
          }),
      kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET,
                 {
                     {I2C_FDATA_FBYTE_OFFSET, 0x77}, {I2C_FDATA_READ, 0x1},
                 });
  EXPECT_EQ(
      dif_i2c_write_byte_raw(&i2c, 0x77,
                             {
                                 .start = false, .stop = false, .read = true,
                             }),
      kDifI2cOk);
}

TEST_F(FifoTest, WriteRawBadArgs) {
  EXPECT_EQ(dif_i2c_write_byte_raw(nullptr, 0xff, {}), kDifI2cBadArg);
  EXPECT_EQ(
      dif_i2c_write_byte_raw(&i2c, 0xff,
                             {
                                 .start = false, .stop = true, .read = true,
                             }),
      kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c, 0xff,
                                   {
                                       .start = false,
                                       .stop = false,
                                       .read = false,
                                       .read_cont = true,
                                       .supress_nak_irq = true,
                                   }),
            kDifI2cBadArg);
}

}  // namespace
}  // namespace dif_i2c_unittest
