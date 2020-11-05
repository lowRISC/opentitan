// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i2c.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "i2c_regs.h"  // Generated.

// We define global namespace == and << to make `dif_i2c_timing_params_t` work
// nicely with EXPECT_EQ.
bool operator==(dif_i2c_config_t a, dif_i2c_config_t b) {
  // We just do a dumb memcmp. The config params struct is essentially an array
  // of half-words, so we won't run into padding issues.
  return std::memcmp(&a, &b, sizeof(dif_i2c_config_t)) == 0;
}

std::ostream &operator<<(std::ostream &os, const dif_i2c_config_t &params) {
  return os << "{\n"
            << "  .scl_time_high_cycles = " << params.scl_time_high_cycles
            << ",\n"
            << "  .scl_time_low_cycles = " << params.scl_time_low_cycles
            << ",\n"
            << "  .rise_cycles = " << params.rise_cycles << ",\n"
            << "  .fall_cycles = " << params.fall_cycles << ",\n"
            << "  .start_signal_setup_cycles = "
            << params.start_signal_setup_cycles << ",\n"
            << "  .start_signal_hold_cycles = "
            << params.start_signal_hold_cycles << ",\n"
            << "  .data_signal_setup_cycles = "
            << params.data_signal_setup_cycles << ",\n"
            << "  .data_signal_hold_cycles = " << params.data_signal_hold_cycles
            << ",\n"
            << "  .stop_signal_setup_cycles = "
            << params.stop_signal_setup_cycles << ",\n"
            << "  .stop_signal_hold_cycles = " << params.stop_signal_hold_cycles
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
  dif_i2c_config_t params, expected;

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  expected = {
      .scl_time_high_cycles = 53,
      .scl_time_low_cycles = 53,
      .rise_cycles = 3,
      .fall_cycles = 3,
      .start_signal_setup_cycles = 53,
      .start_signal_hold_cycles = 45,
      .data_signal_setup_cycles = 3,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 45,
      .stop_signal_hold_cycles = 53,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  expected = {
      .scl_time_high_cycles = 252,
      .scl_time_low_cycles = 235,
      .rise_cycles = 6,
      .fall_cycles = 7,
      .start_signal_setup_cycles = 235,
      .start_signal_hold_cycles = 200,
      .data_signal_setup_cycles = 13,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 200,
      .stop_signal_hold_cycles = 235,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedStandard;
  config.scl_period_nanos = 11000;
  expected = {
      .scl_time_high_cycles = 64,
      .scl_time_low_cycles = 53,
      .rise_cycles = 3,
      .fall_cycles = 3,
      .start_signal_setup_cycles = 53,
      .start_signal_hold_cycles = 45,
      .data_signal_setup_cycles = 3,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 45,
      .stop_signal_hold_cycles = 53,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, FastSpeed) {
  dif_i2c_timing_config_t config;
  dif_i2c_config_t params, expected;

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  expected = {
      .scl_time_high_cycles = 7,
      .scl_time_low_cycles = 15,
      .rise_cycles = 3,
      .fall_cycles = 3,
      .start_signal_setup_cycles = 7,
      .start_signal_hold_cycles = 7,
      .data_signal_setup_cycles = 2,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 7,
      .stop_signal_hold_cycles = 15,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  expected = {
      .scl_time_high_cycles = 47,
      .scl_time_low_cycles = 65,
      .rise_cycles = 6,
      .fall_cycles = 7,
      .start_signal_setup_cycles = 30,
      .start_signal_hold_cycles = 30,
      .data_signal_setup_cycles = 5,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 30,
      .stop_signal_hold_cycles = 65,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigSlow;
  config.lowest_target_device_speed = kDifI2cSpeedFast;
  config.scl_period_nanos = 8000;
  expected = {
      .scl_time_high_cycles = 68,
      .scl_time_low_cycles = 15,
      .rise_cycles = 3,
      .fall_cycles = 3,
      .start_signal_setup_cycles = 7,
      .start_signal_hold_cycles = 7,
      .data_signal_setup_cycles = 2,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 7,
      .stop_signal_hold_cycles = 15,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, FastPlusSpeed) {
  dif_i2c_timing_config_t config;
  dif_i2c_config_t params, expected;

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFastPlus;
  expected = {
      .scl_time_high_cycles = 13,
      .scl_time_low_cycles = 25,
      .rise_cycles = 6,
      .fall_cycles = 7,
      .start_signal_setup_cycles = 13,
      .start_signal_hold_cycles = 13,
      .data_signal_setup_cycles = 3,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 13,
      .stop_signal_hold_cycles = 25,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);

  config = kBaseConfigFast;
  config.lowest_target_device_speed = kDifI2cSpeedFastPlus;
  config.scl_period_nanos = 1500;
  expected = {
      .scl_time_high_cycles = 37,
      .scl_time_low_cycles = 25,
      .rise_cycles = 6,
      .fall_cycles = 7,
      .start_signal_setup_cycles = 13,
      .start_signal_hold_cycles = 13,
      .data_signal_setup_cycles = 3,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 13,
      .stop_signal_hold_cycles = 25,
  };
  EXPECT_EQ(dif_i2c_compute_timing(config, &params), kDifI2cOk);
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, NullArgs) {
  EXPECT_EQ(dif_i2c_compute_timing(kBaseConfigFast, nullptr), kDifI2cBadArg);
}

class I2cTest : public testing::Test, public MmioTest {
 protected:
  dif_i2c_t i2c_ = {.params = {.base_addr = dev().region()}};
};

class ConfigTest : public I2cTest {};

TEST_F(ConfigTest, NormalInit) {
  dif_i2c_config_t config = {
      .scl_time_high_cycles = 252,
      .scl_time_low_cycles = 235,
      .rise_cycles = 6,
      .fall_cycles = 7,
      .start_signal_setup_cycles = 235,
      .start_signal_hold_cycles = 200,
      .data_signal_setup_cycles = 13,
      .data_signal_hold_cycles = 0,
      .stop_signal_setup_cycles = 200,
      .stop_signal_hold_cycles = 235,
  };

  EXPECT_WRITE32(I2C_TIMING0_REG_OFFSET,
                 {
                     {I2C_TIMING0_THIGH_OFFSET, config.scl_time_high_cycles},
                     {I2C_TIMING0_TLOW_OFFSET, config.scl_time_low_cycles},
                 });
  EXPECT_WRITE32(I2C_TIMING1_REG_OFFSET,
                 {
                     {I2C_TIMING1_T_R_OFFSET, config.rise_cycles},
                     {I2C_TIMING1_T_F_OFFSET, config.fall_cycles},
                 });
  EXPECT_WRITE32(
      I2C_TIMING2_REG_OFFSET,
      {
          {I2C_TIMING2_TSU_STA_OFFSET, config.start_signal_setup_cycles},
          {I2C_TIMING2_THD_STA_OFFSET, config.start_signal_hold_cycles},
      });
  EXPECT_WRITE32(
      I2C_TIMING3_REG_OFFSET,
      {
          {I2C_TIMING3_TSU_DAT_OFFSET, config.data_signal_setup_cycles},
          {I2C_TIMING3_THD_DAT_OFFSET, config.data_signal_hold_cycles},
      });
  EXPECT_WRITE32(
      I2C_TIMING4_REG_OFFSET,
      {
          {I2C_TIMING4_TSU_STO_OFFSET, config.stop_signal_setup_cycles},
          {I2C_TIMING4_T_BUF_OFFSET, config.stop_signal_hold_cycles},
      });

  EXPECT_EQ(dif_i2c_configure(&i2c_, config), kDifI2cOk);
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_i2c_configure(nullptr, {}), kDifI2cBadArg);
}

class FifoCtrlTest : public I2cTest {};

TEST_F(FifoCtrlTest, RxReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_RXRST_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_reset_rx_fifo(&i2c_), kDifI2cOk);
}

TEST_F(FifoCtrlTest, RxNullArgs) {
  EXPECT_EQ(dif_i2c_reset_rx_fifo(nullptr), kDifI2cBadArg);
}

TEST_F(FifoCtrlTest, FmtReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_FMTRST_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_reset_fmt_fifo(&i2c_), kDifI2cOk);
}

TEST_F(FifoCtrlTest, FmtNullArgs) {
  EXPECT_EQ(dif_i2c_reset_fmt_fifo(nullptr), kDifI2cBadArg);
}

TEST_F(FifoCtrlTest, SetLevels) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {
                    {
                        I2C_FIFO_CTRL_RXILVL_OFFSET,
                        I2C_FIFO_CTRL_RXILVL_MASK,
                        I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL1,
                    },
                    {
                        I2C_FIFO_CTRL_FMTILVL_OFFSET,
                        I2C_FIFO_CTRL_FMTILVL_MASK,
                        I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL1,
                    },
                });
  EXPECT_EQ(dif_i2c_set_watermarks(&i2c_, kDifI2cLevel1Byte, kDifI2cLevel1Byte),
            kDifI2cOk);

  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {
                    {
                        I2C_FIFO_CTRL_RXILVL_OFFSET,
                        I2C_FIFO_CTRL_RXILVL_MASK,
                        I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL4,
                    },
                    {
                        I2C_FIFO_CTRL_FMTILVL_OFFSET,
                        I2C_FIFO_CTRL_FMTILVL_MASK,
                        I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL16,
                    },
                });
  EXPECT_EQ(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel4Byte, kDifI2cLevel16Byte),
      kDifI2cOk);

  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {
                    {
                        I2C_FIFO_CTRL_RXILVL_OFFSET,
                        I2C_FIFO_CTRL_RXILVL_MASK,
                        I2C_FIFO_CTRL_RXILVL_VALUE_RXLVL30,
                    },
                    {
                        I2C_FIFO_CTRL_FMTILVL_OFFSET,
                        I2C_FIFO_CTRL_FMTILVL_MASK,
                        I2C_FIFO_CTRL_FMTILVL_VALUE_FMTLVL8,
                    },
                });
  EXPECT_EQ(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel30Byte, kDifI2cLevel8Byte),
      kDifI2cOk);

  EXPECT_EQ(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel30Byte, kDifI2cLevel30Byte),
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
                {{I2C_INTR_STATE_FMT_WATERMARK_BIT, 0x1}});
  EXPECT_EQ(
      dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqFmtWatermarkUnderflow, &flag),
      kDifI2cOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK_BIT, 0x0}});
  EXPECT_EQ(
      dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqFmtWatermarkUnderflow, &flag),
      kDifI2cOk);
  EXPECT_FALSE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK_BIT, 0x1}});
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqNak, &flag), kDifI2cOk);
  EXPECT_TRUE(flag);

  EXPECT_READ32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK_BIT, 0x0}});
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqNak, &flag), kDifI2cOk);
  EXPECT_FALSE(flag);
}

TEST_F(IrqTest, GetNullArgs) {
  bool flag;

  EXPECT_EQ(dif_i2c_irq_is_pending(nullptr, kDifI2cIrqNak, &flag),
            kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_irq_is_pending(&i2c_, kDifI2cIrqNak, nullptr),
            kDifI2cBadArg);
}

TEST_F(IrqTest, Clear) {
  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET,
                 {{I2C_INTR_STATE_FMT_WATERMARK_BIT, 0x1}});
  EXPECT_EQ(dif_i2c_irq_acknowledge(&i2c_, kDifI2cIrqFmtWatermarkUnderflow),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_INTR_STATE_REG_OFFSET, {{I2C_INTR_STATE_NAK_BIT, 0x1}});
  EXPECT_EQ(dif_i2c_irq_acknowledge(&i2c_, kDifI2cIrqNak), kDifI2cOk);
}

TEST_F(IrqTest, ClearNullArgs) {
  EXPECT_EQ(dif_i2c_irq_acknowledge(nullptr, kDifI2cIrqNak), kDifI2cBadArg);
}

TEST_F(IrqTest, Enable) {
  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqFmtWatermarkUnderflow,
                                    kDifI2cToggleEnabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_FMT_WATERMARK_BIT, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqFmtWatermarkUnderflow,
                                    kDifI2cToggleDisabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_NAK_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqNak, kDifI2cToggleEnabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_INTR_ENABLE_REG_OFFSET,
                {{I2C_INTR_STATE_NAK_BIT, 0x1, 0x0}});
  EXPECT_EQ(
      dif_i2c_irq_set_enabled(&i2c_, kDifI2cIrqNak, kDifI2cToggleDisabled),
      kDifI2cOk);
}

TEST_F(IrqTest, EnableNullArgs) {
  EXPECT_EQ(
      dif_i2c_irq_set_enabled(nullptr, kDifI2cIrqNak, kDifI2cToggleEnabled),
      kDifI2cBadArg);
}

TEST_F(IrqTest, Force) {
  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET,
                 {{I2C_INTR_TEST_FMT_WATERMARK_BIT, 0x1}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c_, kDifI2cIrqFmtWatermarkUnderflow),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_INTR_TEST_REG_OFFSET, {{I2C_INTR_TEST_NAK_BIT, 0x1}});
  EXPECT_EQ(dif_i2c_irq_force(&i2c_, kDifI2cIrqNak), kDifI2cOk);
}

TEST_F(IrqTest, ForceNullArgs) {
  EXPECT_EQ(dif_i2c_irq_force(nullptr, kDifI2cIrqNak), kDifI2cBadArg);
}

class ControlTest : public I2cTest {};

TEST_F(ControlTest, HostEnable) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_host_set_enabled(&i2c_, kDifI2cToggleEnabled), kDifI2cOk);

  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST_BIT, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_host_set_enabled(&i2c_, kDifI2cToggleDisabled), kDifI2cOk);
}

TEST_F(ControlTest, HostEnableNullArgs) {
  EXPECT_EQ(dif_i2c_host_set_enabled(nullptr, kDifI2cToggleEnabled),
            kDifI2cBadArg);
}

class OverrideTest : public I2cTest {};

TEST_F(OverrideTest, Enable) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN_BIT, 0x1, 0x1}});
  EXPECT_EQ(dif_i2c_override_set_enabled(&i2c_, kDifI2cToggleEnabled),
            kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN_BIT, 0x1, 0x0}});
  EXPECT_EQ(dif_i2c_override_set_enabled(&i2c_, kDifI2cToggleDisabled),
            kDifI2cOk);
}

TEST_F(OverrideTest, EnableNullArgs) {
  EXPECT_EQ(dif_i2c_override_set_enabled(nullptr, kDifI2cToggleEnabled),
            kDifI2cBadArg);
}

TEST_F(OverrideTest, Drive) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x0},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x0},
                                     });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c_, false, false), kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x0},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x1},
                                     });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c_, false, true), kDifI2cOk);

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x1},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x1},
                                     });
  EXPECT_EQ(dif_i2c_override_drive_pins(&i2c_, true, true), kDifI2cOk);
}

TEST_F(OverrideTest, DriveNullArgs) {
  EXPECT_EQ(dif_i2c_override_drive_pins(nullptr, false, false), kDifI2cBadArg);
}

TEST_F(OverrideTest, Sample) {
  uint16_t scl, sda;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c_, &scl, &sda), kDifI2cOk);
  EXPECT_EQ(scl, 0x3847);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c_, nullptr, &sda), kDifI2cOk);
  EXPECT_EQ(scl, 0x0);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_override_sample_pins(&i2c_, &scl, nullptr), kDifI2cOk);
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
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c_, &rx, &fmt), kDifI2cOk);
  EXPECT_EQ(rx, 0x7);
  EXPECT_EQ(fmt, 0x29);

  rx = 0, fmt = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c_, nullptr, &fmt), kDifI2cOk);
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(fmt, 0x29);

  rx = 0, fmt = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_EQ(dif_i2c_get_fifo_levels(&i2c_, &rx, nullptr), kDifI2cOk);
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

  EXPECT_EQ(dif_i2c_read_byte(&i2c_, &val), kDifI2cOk);
  EXPECT_EQ(val, 0xab);
  EXPECT_EQ(dif_i2c_read_byte(&i2c_, &val), kDifI2cOk);
  EXPECT_EQ(val, 0xcd);
  EXPECT_EQ(dif_i2c_read_byte(&i2c_, nullptr), kDifI2cOk);
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
  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x44},
                                           {I2C_FDATA_START_BIT, 0x1},
                                       });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c_, 0x44,
                                   {
                                       .start = true,
                                   }),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x55},
                                       });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c_, 0x55, {}), kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x66},
                                           {I2C_FDATA_STOP_BIT, 0x1},
                                           {I2C_FDATA_NAKOK_BIT, 0x1},
                                       });
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c_, 0x66,
                                   {
                                       .start = false,
                                       .stop = true,
                                       .read = false,
                                       .read_cont = false,
                                       .suppress_nak_irq = true,
                                   }),
            kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x00},
                                           {I2C_FDATA_READ_BIT, 0x1},
                                           {I2C_FDATA_RCONT_BIT, 0x1},
                                       });
  EXPECT_EQ(
      dif_i2c_write_byte_raw(
          &i2c_, 0x00,
          {
              .start = false, .stop = false, .read = true, .read_cont = true,
          }),
      kDifI2cOk);

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x77},
                                           {I2C_FDATA_READ_BIT, 0x1},
                                       });
  EXPECT_EQ(
      dif_i2c_write_byte_raw(&i2c_, 0x77,
                             {
                                 .start = false, .stop = false, .read = true,
                             }),
      kDifI2cOk);
}

TEST_F(FifoTest, WriteRawBadArgs) {
  EXPECT_EQ(dif_i2c_write_byte_raw(nullptr, 0xff, {}), kDifI2cBadArg);
  EXPECT_EQ(
      dif_i2c_write_byte_raw(&i2c_, 0xff,
                             {
                                 .start = false, .stop = true, .read = true,
                             }),
      kDifI2cBadArg);
  EXPECT_EQ(dif_i2c_write_byte_raw(&i2c_, 0xff,
                                   {
                                       .start = false,
                                       .stop = false,
                                       .read = false,
                                       .read_cont = true,
                                       .suppress_nak_irq = true,
                                   }),
            kDifI2cBadArg);
}

}  // namespace
}  // namespace dif_i2c_unittest
