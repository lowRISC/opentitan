// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_i2c.h"

#include <cstring>
#include <limits>
#include <ostream>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

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

// We define global namespace == and << to make `dif_i2c_status_t` work
// nicely with EXPECT_EQ.
bool operator==(dif_i2c_status_t a, dif_i2c_status_t b) {
  return a.enable_host == b.enable_host && a.enable_target == b.enable_target &&
         a.line_loopback == b.line_loopback &&
         a.fmt_fifo_full == b.fmt_fifo_full &&
         a.rx_fifo_full == b.rx_fifo_full &&
         a.fmt_fifo_empty == b.fmt_fifo_empty &&
         a.rx_fifo_empty == b.rx_fifo_empty && a.host_idle == b.host_idle &&
         a.target_idle == b.target_idle && a.tx_fifo_full == b.tx_fifo_full &&
         a.acq_fifo_full == b.acq_fifo_full &&
         a.tx_fifo_empty == b.tx_fifo_empty &&
         a.acq_fifo_empty == b.acq_fifo_empty;
}

std::ostream &operator<<(std::ostream &os, const dif_i2c_status_t &params) {
  return os << "{\n"
            << "  .enable_host = " << params.enable_host << ",\n"
            << "  .enable_target = " << params.enable_target << ",\n"
            << "  .line_loopback = " << params.line_loopback << ",\n"
            << "  .fmt_fifo_full = " << params.fmt_fifo_full << ",\n"
            << "  .rx_fifo_full = " << params.rx_fifo_full << ",\n"
            << "  .fmt_fifo_empty = " << params.fmt_fifo_empty << ",\n"
            << "  .rx_fifo_empty = " << params.rx_fifo_empty << ",\n"
            << "  .host_idle = " << params.host_idle << ",\n"
            << "  .target_idle = " << params.target_idle << ",\n"
            << "  .tx_fifo_full = " << params.tx_fifo_full << ",\n"
            << "  .acq_fifo_full = " << params.acq_fifo_full << ",\n"
            << "  .tx_fifo_empty = " << params.tx_fifo_empty << ",\n"
            << "  .acq_fifo_empty = " << params.acq_fifo_empty << ",\n"
            << "}";
}

namespace dif_i2c_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

class I2cTest : public testing::Test, public MmioTest {
 protected:
  dif_i2c_t i2c_ = {.base_addr = dev().region()};
};

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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 45,
      .stop_signal_hold_cycles = 53,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 200,
      .stop_signal_hold_cycles = 235,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 45,
      .stop_signal_hold_cycles = 53,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 7,
      .stop_signal_hold_cycles = 15,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 30,
      .stop_signal_hold_cycles = 65,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 7,
      .stop_signal_hold_cycles = 15,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 13,
      .stop_signal_hold_cycles = 25,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
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
      .data_signal_hold_cycles = 1,
      .stop_signal_setup_cycles = 13,
      .stop_signal_hold_cycles = 25,
  };
  EXPECT_DIF_OK(dif_i2c_compute_timing(config, &params));
  EXPECT_EQ(params, expected);
}

TEST(ComputeTimingTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_compute_timing(kBaseConfigFast, nullptr));
}

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
      .data_signal_hold_cycles = 1,
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

  EXPECT_DIF_OK(dif_i2c_configure(&i2c_, config));

  dif_i2c_status status, expectedStatus;
  EXPECT_READ32(I2C_CTRL_REG_OFFSET, 0x00000003);    // Host and Target active
  EXPECT_READ32(I2C_STATUS_REG_OFFSET, 0x0000033c);  // All empty and idle
  EXPECT_DIF_OK(dif_i2c_get_status(&i2c_, &status));
  expectedStatus = {
      .enable_host = true,
      .enable_target = true,
      .fmt_fifo_empty = true,
      .rx_fifo_empty = true,
      .host_idle = true,
      .target_idle = true,
      .tx_fifo_empty = true,
      .acq_fifo_empty = true,
  };
  EXPECT_EQ(status, expectedStatus);
}

TEST_F(ConfigTest, NullArgs) {
  dif_i2c_status status;
  EXPECT_DIF_BADARG(dif_i2c_get_status(nullptr, &status));
  EXPECT_DIF_BADARG(dif_i2c_get_status(&i2c_, nullptr));
  EXPECT_DIF_BADARG(dif_i2c_configure(nullptr, {}));
}

class FifoCtrlTest : public I2cTest {};

TEST_F(FifoCtrlTest, RxReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_RXRST_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_reset_rx_fifo(&i2c_));
}

TEST_F(FifoCtrlTest, RxNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_reset_rx_fifo(nullptr));
}

TEST_F(FifoCtrlTest, FmtReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_FMTRST_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_reset_fmt_fifo(&i2c_));
}

TEST_F(FifoCtrlTest, FmtNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_reset_fmt_fifo(nullptr));
}

TEST_F(FifoCtrlTest, AcqReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_ACQRST_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_reset_acq_fifo(&i2c_));
}

TEST_F(FifoCtrlTest, AcqNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_reset_acq_fifo(nullptr));
}

TEST_F(FifoCtrlTest, TxReset) {
  EXPECT_MASK32(I2C_FIFO_CTRL_REG_OFFSET,
                {{I2C_FIFO_CTRL_TXRST_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_reset_tx_fifo(&i2c_));
}

TEST_F(FifoCtrlTest, TxNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_reset_tx_fifo(nullptr));
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
  EXPECT_DIF_OK(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel1Byte, kDifI2cLevel1Byte));

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
  EXPECT_DIF_OK(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel4Byte, kDifI2cLevel16Byte));

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
  EXPECT_DIF_OK(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel30Byte, kDifI2cLevel8Byte));

  EXPECT_DIF_BADARG(
      dif_i2c_set_watermarks(&i2c_, kDifI2cLevel30Byte, kDifI2cLevel30Byte));
}

TEST_F(FifoCtrlTest, SetLevelsNullArgs) {
  EXPECT_DIF_BADARG(
      dif_i2c_set_watermarks(nullptr, kDifI2cLevel4Byte, kDifI2cLevel16Byte));
}

class ControlTest : public I2cTest {};

TEST_F(ControlTest, HostEnable) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_host_set_enabled(&i2c_, kDifToggleEnabled));

  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLEHOST_BIT, 0x1, 0x0}});
  EXPECT_DIF_OK(dif_i2c_host_set_enabled(&i2c_, kDifToggleDisabled));
}

TEST_F(ControlTest, HostEnableNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_host_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(ControlTest, DeviceEnable) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLETARGET_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_device_set_enabled(&i2c_, kDifToggleEnabled));

  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_ENABLETARGET_BIT, 0x1, 0x0}});
  EXPECT_DIF_OK(dif_i2c_device_set_enabled(&i2c_, kDifToggleDisabled));
}

TEST_F(ControlTest, DeviceEnableNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_device_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(ControlTest, LLPBK) {
  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_LLPBK_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_line_loopback_set_enabled(&i2c_, kDifToggleEnabled));

  EXPECT_MASK32(I2C_CTRL_REG_OFFSET, {{I2C_CTRL_LLPBK_BIT, 0x1, 0x0}});
  EXPECT_DIF_OK(dif_i2c_line_loopback_set_enabled(&i2c_, kDifToggleDisabled));
}

TEST_F(ControlTest, LLPBKNullArgs) {
  EXPECT_DIF_BADARG(
      dif_i2c_line_loopback_set_enabled(nullptr, kDifToggleEnabled));
}

class OverrideTest : public I2cTest {};

TEST_F(OverrideTest, Enable) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN_BIT, 0x1, 0x1}});
  EXPECT_DIF_OK(dif_i2c_override_set_enabled(&i2c_, kDifToggleEnabled));

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {{I2C_OVRD_TXOVRDEN_BIT, 0x1, 0x0}});
  EXPECT_DIF_OK(dif_i2c_override_set_enabled(&i2c_, kDifToggleDisabled));
}

TEST_F(OverrideTest, EnableNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_override_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(OverrideTest, Drive) {
  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x0},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x0},
                                     });
  EXPECT_DIF_OK(dif_i2c_override_drive_pins(&i2c_, false, false));

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x0},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x1},
                                     });
  EXPECT_DIF_OK(dif_i2c_override_drive_pins(&i2c_, false, true));

  EXPECT_MASK32(I2C_OVRD_REG_OFFSET, {
                                         {I2C_OVRD_SCLVAL_BIT, 0x1, 0x1},
                                         {I2C_OVRD_SDAVAL_BIT, 0x1, 0x1},
                                     });
  EXPECT_DIF_OK(dif_i2c_override_drive_pins(&i2c_, true, true));
}

TEST_F(OverrideTest, DriveNullArgs) {
  EXPECT_DIF_BADARG(dif_i2c_override_drive_pins(nullptr, false, false));
}

TEST_F(OverrideTest, Sample) {
  uint16_t scl, sda;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_override_sample_pins(&i2c_, &scl, &sda));
  EXPECT_EQ(scl, 0x3847);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_override_sample_pins(&i2c_, nullptr, &sda));
  EXPECT_EQ(scl, 0x0);
  EXPECT_EQ(sda, 0x1029);

  scl = 0, sda = 0;
  EXPECT_READ32(I2C_VAL_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_override_sample_pins(&i2c_, &scl, nullptr));
  EXPECT_EQ(scl, 0x3847);
  EXPECT_EQ(sda, 0x0);
}

TEST_F(OverrideTest, SampleNullArgs) {
  uint16_t scl, sda;
  EXPECT_DIF_BADARG(dif_i2c_override_sample_pins(nullptr, &scl, &sda));
}

class FifoTest : public I2cTest {};

TEST_F(FifoTest, GetLevels) {
  uint8_t rx, fmt, tx, acq;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_get_fifo_levels(&i2c_, &fmt, &rx, &tx, &acq));
  EXPECT_EQ(fmt, 0x47);
  EXPECT_EQ(rx, 0x29);
  EXPECT_EQ(tx, 0x38);
  EXPECT_EQ(acq, 0x10);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_get_fifo_levels(&i2c_, &fmt, &rx, nullptr, nullptr));
  EXPECT_EQ(fmt, 0x47);
  EXPECT_EQ(rx, 0x29);
  EXPECT_EQ(tx, 0x0);
  EXPECT_EQ(acq, 0x0);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(
      dif_i2c_get_fifo_levels(&i2c_, &fmt, nullptr, nullptr, nullptr));
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(fmt, 0x47);
  EXPECT_EQ(tx, 0x0);
  EXPECT_EQ(acq, 0x0);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_get_fifo_levels(&i2c_, nullptr, &rx, nullptr, nullptr));
  EXPECT_EQ(rx, 0x29);
  EXPECT_EQ(fmt, 0x0);
  EXPECT_EQ(tx, 0x0);
  EXPECT_EQ(acq, 0x0);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_get_fifo_levels(&i2c_, nullptr, nullptr, &tx, &acq));
  EXPECT_EQ(fmt, 0x0);
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(tx, 0x38);
  EXPECT_EQ(acq, 0x10);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(dif_i2c_get_fifo_levels(&i2c_, nullptr, nullptr, &tx, nullptr));
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(fmt, 0x0);
  EXPECT_EQ(tx, 0x38);
  EXPECT_EQ(acq, 0x0);

  rx = 0, fmt = 0, tx = 0, acq = 0;
  EXPECT_READ32(I2C_FIFO_STATUS_REG_OFFSET, 0x10293847);
  EXPECT_DIF_OK(
      dif_i2c_get_fifo_levels(&i2c_, nullptr, nullptr, nullptr, &acq));
  EXPECT_EQ(rx, 0x0);
  EXPECT_EQ(fmt, 0x0);
  EXPECT_EQ(tx, 0x0);
  EXPECT_EQ(acq, 0x10);
}

TEST_F(FifoTest, GetLevelsNullArgs) {
  uint8_t rx, fmt;
  EXPECT_DIF_BADARG(
      dif_i2c_get_fifo_levels(nullptr, &rx, &fmt, nullptr, nullptr));
}

TEST_F(FifoTest, Read) {
  uint8_t val;

  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xab);
  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xcd);
  EXPECT_READ32(I2C_RDATA_REG_OFFSET, 0xef);

  EXPECT_DIF_OK(dif_i2c_read_byte(&i2c_, &val));
  EXPECT_EQ(val, 0xab);
  EXPECT_DIF_OK(dif_i2c_read_byte(&i2c_, &val));
  EXPECT_EQ(val, 0xcd);
  EXPECT_DIF_OK(dif_i2c_read_byte(&i2c_, nullptr));
  EXPECT_EQ(val, 0xcd);
}

TEST_F(FifoTest, ReadNullArgs) {
  uint8_t val;
  EXPECT_DIF_BADARG(dif_i2c_read_byte(nullptr, &val));
}

TEST_F(FifoTest, Acquire) {
  uint8_t val;
  dif_i2c_signal_t signal;

  EXPECT_READ32(I2C_ACQDATA_REG_OFFSET, 0x0ab);
  EXPECT_READ32(I2C_ACQDATA_REG_OFFSET, 0x3cd);
  EXPECT_READ32(I2C_ACQDATA_REG_OFFSET, 0x2ef);
  EXPECT_READ32(I2C_ACQDATA_REG_OFFSET, 0x101);

  EXPECT_DIF_OK(dif_i2c_acquire_byte(&i2c_, &val, &signal));
  EXPECT_EQ(val, 0xab);
  EXPECT_EQ(signal, kDifI2cSignalNone);
  EXPECT_DIF_OK(dif_i2c_acquire_byte(&i2c_, &val, &signal));
  EXPECT_EQ(val, 0xcd);
  EXPECT_EQ(signal, kDifI2cSignalRepeat);
  EXPECT_DIF_OK(dif_i2c_acquire_byte(&i2c_, nullptr, &signal));
  EXPECT_EQ(val, 0xcd);
  EXPECT_EQ(signal, kDifI2cSignalStop);
  EXPECT_DIF_OK(dif_i2c_acquire_byte(&i2c_, &val, nullptr));
  EXPECT_EQ(val, 0x01);
  EXPECT_EQ(signal, kDifI2cSignalStop);
}

TEST_F(FifoTest, AcqNullArgs) {
  uint8_t val;
  dif_i2c_signal_t signal;

  EXPECT_DIF_BADARG(dif_i2c_acquire_byte(nullptr, &val, &signal));
}

TEST_F(FifoTest, WriteRaw) {
  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x44},
                                           {I2C_FDATA_START_BIT, 0x1},
                                       });
  EXPECT_DIF_OK(dif_i2c_write_byte_raw(&i2c_, 0x44,
                                       {
                                           .start = true,
                                       }));

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x55},
                                       });
  EXPECT_DIF_OK(dif_i2c_write_byte_raw(&i2c_, 0x55, {}));

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x66},
                                           {I2C_FDATA_STOP_BIT, 0x1},
                                           {I2C_FDATA_NAKOK_BIT, 0x1},
                                       });
  EXPECT_DIF_OK(dif_i2c_write_byte_raw(&i2c_, 0x66,
                                       {
                                           .stop = true,
                                           .suppress_nak_irq = true,
                                       }));

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x00},
                                           {I2C_FDATA_READ_BIT, 0x1},
                                           {I2C_FDATA_RCONT_BIT, 0x1},
                                       });
  EXPECT_DIF_OK(dif_i2c_write_byte_raw(&i2c_, 0x00,
                                       {
                                           .read = true,
                                           .read_cont = true,
                                       }));

  EXPECT_WRITE32(I2C_FDATA_REG_OFFSET, {
                                           {I2C_FDATA_FBYTE_OFFSET, 0x77},
                                           {I2C_FDATA_READ_BIT, 0x1},
                                       });
  EXPECT_DIF_OK(dif_i2c_write_byte_raw(&i2c_, 0x77,
                                       {
                                           .read = true,
                                       }));
}

TEST_F(FifoTest, WriteRawBadArgs) {
  EXPECT_DIF_BADARG(dif_i2c_write_byte_raw(nullptr, 0xff, {}));
  EXPECT_DIF_BADARG(dif_i2c_write_byte_raw(&i2c_, 0xff,
                                           {
                                               .start = true,
                                               .read = true,
                                           }));
  EXPECT_DIF_BADARG(dif_i2c_write_byte_raw(&i2c_, 0xff,
                                           {
                                               .read_cont = true,
                                               .suppress_nak_irq = true,
                                           }));
}

TEST_F(FifoTest, TransmitByte) {
  EXPECT_WRITE32(I2C_TXDATA_REG_OFFSET, 0x00000044);
  EXPECT_DIF_OK(dif_i2c_transmit_byte(&i2c_, 0x44));
}

TEST_F(FifoTest, TransmitBadArgs) {
  EXPECT_DIF_BADARG(dif_i2c_transmit_byte(nullptr, 0xff));
}

class StretchTest : public I2cTest {};

TEST_F(StretchTest, ConfigTimeouts) {
  EXPECT_WRITE32(I2C_TIMEOUT_CTRL_REG_OFFSET, 0x81234567);
  EXPECT_DIF_OK(dif_i2c_enable_clock_stretching_timeout(
      &i2c_, kDifToggleEnabled, 0x01234567));
  EXPECT_WRITE32(I2C_HOST_TIMEOUT_CTRL_REG_OFFSET, 0x81234567);
  EXPECT_DIF_OK(dif_i2c_set_host_timeout(&i2c_, 0x81234567));
}

TEST_F(StretchTest, ConfigTimeoutsBadArgs) {
  EXPECT_DIF_BADARG(dif_i2c_enable_clock_stretching_timeout(
      nullptr, kDifToggleEnabled, 0x01234567));
  EXPECT_DIF_BADARG(dif_i2c_set_host_timeout(nullptr, 0x81234567));
}

// Assemble 2 Ids to the byte to form the expections checked in the address test
uint32_t assemble_address(dif_i2c_id_t *id0, dif_i2c_id_t *id1) {
  uint32_t config = 0x00000000;
  if (id0 == NULL) {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS0_FIELD, 0x7f);
  } else {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS0_FIELD,
                                    id0->address);
    config =
        bitfield_field32_write(config, I2C_TARGET_ID_MASK0_FIELD, id0->mask);
  }

  if (id1 == NULL) {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS1_FIELD, 0x7f);
  } else {
    config = bitfield_field32_write(config, I2C_TARGET_ID_ADDRESS1_FIELD,
                                    id1->address);
    config =
        bitfield_field32_write(config, I2C_TARGET_ID_MASK1_FIELD, id1->mask);
  }
  return config;
}

class AddressTest : public I2cTest {};
TEST_F(AddressTest, SetDeviceAddress) {
  // dif_i2c_id_t id0 = NULL, id1 = NULL;
  EXPECT_WRITE32(I2C_TARGET_ID_REG_OFFSET, assemble_address(nullptr, nullptr));
  EXPECT_DIF_OK(dif_i2c_set_device_id(&i2c_, nullptr, nullptr));

  dif_i2c_id_t id0 = {.mask = 0x12, .address = 0x34};
  EXPECT_WRITE32(I2C_TARGET_ID_REG_OFFSET, assemble_address(&id0, nullptr));
  EXPECT_DIF_OK(dif_i2c_set_device_id(&i2c_, &id0, nullptr));

  dif_i2c_id_t id1 = {.mask = 0x56, .address = 0x78};
  EXPECT_WRITE32(I2C_TARGET_ID_REG_OFFSET, assemble_address(nullptr, &id1));
  EXPECT_DIF_OK(dif_i2c_set_device_id(&i2c_, nullptr, &id1));

  EXPECT_WRITE32(I2C_TARGET_ID_REG_OFFSET, assemble_address(&id0, &id1));
  EXPECT_DIF_OK(dif_i2c_set_device_id(&i2c_, &id0, &id1));
}

TEST_F(AddressTest, SetAddressBadArgs) {
  dif_i2c_id_t id0, id1;
  EXPECT_DIF_BADARG(dif_i2c_set_device_id(nullptr, &id0, &id1));
}

}  // namespace
}  // namespace dif_i2c_unittest
