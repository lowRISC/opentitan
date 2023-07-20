// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_pinmux.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "pinmux_regs.h"  // Generated.

namespace dif_pinmux_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class PinmuxTest : public Test, public MmioTest {
 protected:
  void SetUp() { ASSERT_DIF_OK(dif_pinmux_init(dev().region(), &dif_pinmux_)); }

  dif_pinmux_t dif_pinmux_;
};

TEST_F(PinmuxTest, NullArgs) {
  dif_pinmux_index_t index_arg{};
  dif_pinmux_lock_target_t lock_arg{};
  bool bool_arg{};
  EXPECT_DIF_BADARG(dif_pinmux_lock(nullptr, index_arg, lock_arg));
  EXPECT_DIF_BADARG(
      dif_pinmux_is_locked(nullptr, index_arg, lock_arg, &bool_arg));
  EXPECT_DIF_BADARG(
      dif_pinmux_is_locked(&dif_pinmux_, index_arg, lock_arg, nullptr));
  EXPECT_DIF_BADARG(dif_pinmux_input_select(nullptr, index_arg, index_arg));
  EXPECT_DIF_BADARG(dif_pinmux_output_select(nullptr, index_arg, index_arg));

  dif_pinmux_pad_attr_t pad_attr_arg{};
  dif_pinmux_pad_kind_t pad_kind_arg{};
  EXPECT_DIF_BADARG(dif_pinmux_pad_write_attrs(nullptr, index_arg, pad_kind_arg,
                                               pad_attr_arg, &pad_attr_arg));
  EXPECT_DIF_BADARG(dif_pinmux_pad_write_attrs(
      &dif_pinmux_, index_arg, pad_kind_arg, pad_attr_arg, nullptr));
  EXPECT_DIF_BADARG(dif_pinmux_pad_get_attrs(nullptr, index_arg, pad_kind_arg,
                                             &pad_attr_arg));
  EXPECT_DIF_BADARG(
      dif_pinmux_pad_get_attrs(&dif_pinmux_, index_arg, pad_kind_arg, nullptr));

  dif_pinmux_sleep_mode_t sleep_mode_arg{};
  EXPECT_DIF_BADARG(dif_pinmux_pad_sleep_enable(nullptr, index_arg,
                                                pad_kind_arg, sleep_mode_arg));
  EXPECT_DIF_BADARG(
      dif_pinmux_pad_sleep_disable(nullptr, index_arg, pad_kind_arg));
  EXPECT_DIF_BADARG(dif_pinmux_pad_sleep_get_state(nullptr, index_arg,
                                                   pad_kind_arg, &bool_arg));
  EXPECT_DIF_BADARG(dif_pinmux_pad_sleep_get_state(&dif_pinmux_, index_arg,
                                                   pad_kind_arg, nullptr));
  EXPECT_DIF_BADARG(
      dif_pinmux_pad_sleep_clear_state(nullptr, index_arg, pad_kind_arg));

  dif_pinmux_wakeup_config_t wakeup_arg{};
  EXPECT_DIF_BADARG(
      dif_pinmux_wakeup_detector_enable(nullptr, index_arg, wakeup_arg));
  EXPECT_DIF_BADARG(dif_pinmux_wakeup_detector_disable(nullptr, index_arg));
  EXPECT_DIF_BADARG(dif_pinmux_wakeup_cause_clear(nullptr));

  uint32_t uint32_arg{};
  EXPECT_DIF_BADARG(dif_pinmux_wakeup_cause_get(nullptr, &uint32_arg));
}

TEST_F(PinmuxTest, LockConfig) {
  bool is_locked;
  EXPECT_READ32(PINMUX_MIO_PERIPH_INSEL_REGWEN_0_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_pinmux_is_locked(&dif_pinmux_, /*index=*/0,
                                     kDifPinmuxLockTargetInsel, &is_locked));
  EXPECT_FALSE(is_locked);

  EXPECT_READ32(PINMUX_DIO_PAD_SLEEP_REGWEN_1_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_pinmux_is_locked(&dif_pinmux_, /*index=*/1,
                                     kDifPinmuxLockTargetDioSleep, &is_locked));
  EXPECT_TRUE(is_locked);

  EXPECT_WRITE32(PINMUX_MIO_PAD_SLEEP_REGWEN_2_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_pinmux_lock(&dif_pinmux_, /*index=*/2, kDifPinmuxLockTargetMioSleep));
}

TEST_F(PinmuxTest, InputSelection) {
  EXPECT_READ32(PINMUX_MIO_PERIPH_INSEL_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_input_select(&dif_pinmux_, /*peripheral_input=*/0,
                                    /*insel=*/3),
            kDifLocked);

  EXPECT_READ32(PINMUX_MIO_PERIPH_INSEL_REGWEN_2_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_MIO_PERIPH_INSEL_2_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_pinmux_input_select(&dif_pinmux_, /*peripheral_input=*/2,
                                        /*insel=*/1));
}

TEST_F(PinmuxTest, OutputSelection) {
  EXPECT_READ32(PINMUX_MIO_OUTSEL_REGWEN_1_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_output_select(&dif_pinmux_, /*mio_pad_output=*/1,
                                     /*outsel=*/3),
            kDifLocked);

  EXPECT_READ32(PINMUX_MIO_OUTSEL_REGWEN_3_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_MIO_OUTSEL_3_REG_OFFSET, 4);
  EXPECT_DIF_OK(dif_pinmux_output_select(&dif_pinmux_, /*mio_pad_output=*/3,
                                         /*outsel=*/4));
}

TEST_F(PinmuxTest, PadAttributes) {
  dif_pinmux_pad_attr_t attrs = {
      .slew_rate = 2,
      .drive_strength = 5,
      .flags = static_cast<dif_pinmux_pad_attr_flags_t>(
          kDifPinmuxPadAttrInvertLevel | kDifPinmuxPadAttrPullResistorEnable |
          kDifPinmuxPadAttrPullResistorUp),
  };
  dif_pinmux_pad_attr_t attrs_check;
  EXPECT_READ32(PINMUX_MIO_PAD_ATTR_REGWEN_1_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_pad_write_attrs(&dif_pinmux_, /*pad=*/1,
                                       /*type=*/kDifPinmuxPadKindMio, attrs,
                                       &attrs_check),
            kDifLocked);

  EXPECT_READ32(PINMUX_DIO_PAD_ATTR_REGWEN_2_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_pad_write_attrs(&dif_pinmux_, /*pad=*/2,
                                       /*type=*/kDifPinmuxPadKindDio, attrs,
                                       &attrs_check),
            kDifLocked);

  EXPECT_READ32(PINMUX_MIO_PAD_ATTR_REGWEN_1_REG_OFFSET, 1);
  EXPECT_READ32(PINMUX_MIO_PAD_ATTR_1_REG_OFFSET, 0);
  EXPECT_WRITE32(PINMUX_MIO_PAD_ATTR_1_REG_OFFSET,
                 {
                     {PINMUX_MIO_PAD_ATTR_1_INVERT_1_BIT, 1},
                     {PINMUX_MIO_PAD_ATTR_1_PULL_EN_1_BIT, 1},
                     {PINMUX_MIO_PAD_ATTR_1_PULL_SELECT_1_BIT, 1},
                     {PINMUX_MIO_PAD_ATTR_1_SLEW_RATE_1_OFFSET, 2},
                     {PINMUX_MIO_PAD_ATTR_1_DRIVE_STRENGTH_1_OFFSET, 5},
                 });
  EXPECT_READ32(PINMUX_MIO_PAD_ATTR_1_REG_OFFSET,
                {
                    {PINMUX_MIO_PAD_ATTR_1_INVERT_1_BIT, 1},
                    {PINMUX_MIO_PAD_ATTR_1_PULL_EN_1_BIT, 1},
                    {PINMUX_MIO_PAD_ATTR_1_PULL_SELECT_1_BIT, 1},
                    {PINMUX_MIO_PAD_ATTR_1_SLEW_RATE_1_OFFSET, 2},
                    {PINMUX_MIO_PAD_ATTR_1_DRIVE_STRENGTH_1_OFFSET, 5},
                });
  EXPECT_DIF_OK(dif_pinmux_pad_write_attrs(&dif_pinmux_, /*pad=*/1,
                                           /*type=*/kDifPinmuxPadKindMio, attrs,
                                           &attrs_check));
  EXPECT_EQ(attrs_check.slew_rate, attrs.slew_rate);
  EXPECT_EQ(attrs_check.drive_strength, attrs.drive_strength);
  EXPECT_EQ(attrs_check.flags, attrs.flags);

  EXPECT_READ32(PINMUX_DIO_PAD_ATTR_REGWEN_3_REG_OFFSET, 1);
  EXPECT_READ32(PINMUX_DIO_PAD_ATTR_3_REG_OFFSET, 0);
  EXPECT_WRITE32(PINMUX_DIO_PAD_ATTR_3_REG_OFFSET,
                 {
                     {PINMUX_DIO_PAD_ATTR_3_INVERT_3_BIT, 1},
                     {PINMUX_DIO_PAD_ATTR_3_PULL_EN_3_BIT, 1},
                     {PINMUX_DIO_PAD_ATTR_3_PULL_SELECT_3_BIT, 1},
                     {PINMUX_DIO_PAD_ATTR_3_SLEW_RATE_3_OFFSET, 2},
                     {PINMUX_DIO_PAD_ATTR_3_DRIVE_STRENGTH_3_OFFSET, 5},
                 });
  EXPECT_READ32(PINMUX_DIO_PAD_ATTR_3_REG_OFFSET,
                {
                    {PINMUX_DIO_PAD_ATTR_3_INVERT_3_BIT, 0},
                    {PINMUX_DIO_PAD_ATTR_3_PULL_EN_3_BIT, 1},
                    {PINMUX_DIO_PAD_ATTR_3_PULL_SELECT_3_BIT, 1},
                    {PINMUX_DIO_PAD_ATTR_3_SLEW_RATE_3_OFFSET, 2},
                    {PINMUX_DIO_PAD_ATTR_3_DRIVE_STRENGTH_3_OFFSET, 5},
                });
  EXPECT_EQ(dif_pinmux_pad_write_attrs(&dif_pinmux_, /*pad=*/3,
                                       /*type=*/kDifPinmuxPadKindDio, attrs,
                                       &attrs_check),
            kDifError);
  EXPECT_EQ(attrs_check.slew_rate, attrs.slew_rate);
  EXPECT_EQ(attrs_check.drive_strength, attrs.drive_strength);
  EXPECT_EQ(attrs_check.flags, kDifPinmuxPadAttrPullResistorEnable |
                                   kDifPinmuxPadAttrPullResistorUp);

  EXPECT_READ32(PINMUX_MIO_PAD_ATTR_1_REG_OFFSET,
                {
                    {PINMUX_MIO_PAD_ATTR_1_KEEPER_EN_1_BIT, 1},
                    {PINMUX_MIO_PAD_ATTR_1_OD_EN_1_BIT, 1},
                    {PINMUX_MIO_PAD_ATTR_1_SLEW_RATE_1_OFFSET, 1},
                    {PINMUX_MIO_PAD_ATTR_1_DRIVE_STRENGTH_1_OFFSET, 3},
                });
  EXPECT_DIF_OK(dif_pinmux_pad_get_attrs(
      &dif_pinmux_, /*pad=*/1, /*type=*/kDifPinmuxPadKindMio, &attrs_check));
  EXPECT_EQ(attrs_check.slew_rate, 1);
  EXPECT_EQ(attrs_check.drive_strength, 3);
  EXPECT_EQ(attrs_check.flags,
            kDifPinmuxPadAttrKeeper | kDifPinmuxPadAttrOpenDrain);
}

TEST_F(PinmuxTest, SleepModeConfig) {
  EXPECT_READ32(PINMUX_MIO_PAD_SLEEP_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_pinmux_pad_sleep_enable(&dif_pinmux_, /*pad=*/0, kDifPinmuxPadKindMio,
                                  kDifPinmuxSleepModeHighZ),
      kDifLocked);

  EXPECT_READ32(PINMUX_DIO_PAD_SLEEP_REGWEN_1_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_pad_sleep_disable(&dif_pinmux_, /*pad=*/1,
                                         kDifPinmuxPadKindDio),
            kDifLocked);

  EXPECT_READ32(PINMUX_MIO_PAD_SLEEP_REGWEN_1_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_MIO_PAD_SLEEP_MODE_1_REG_OFFSET,
                 kDifPinmuxSleepModeHighZ);
  EXPECT_WRITE32(PINMUX_MIO_PAD_SLEEP_EN_1_REG_OFFSET,
                 {{PINMUX_MIO_PAD_SLEEP_EN_1_EN_1_BIT, 1}});
  EXPECT_DIF_OK(dif_pinmux_pad_sleep_enable(
      &dif_pinmux_, /*pad=*/1, kDifPinmuxPadKindMio, kDifPinmuxSleepModeHighZ));

  EXPECT_READ32(PINMUX_DIO_PAD_SLEEP_REGWEN_2_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_DIO_PAD_SLEEP_EN_2_REG_OFFSET,
                 {{PINMUX_DIO_PAD_SLEEP_EN_2_EN_2_BIT, 0}});
  EXPECT_DIF_OK(dif_pinmux_pad_sleep_disable(&dif_pinmux_, /*pad=*/2,
                                             kDifPinmuxPadKindDio));
}

TEST_F(PinmuxTest, SleepStatus) {
  bool in_sleep_mode;
  EXPECT_READ32(PINMUX_MIO_PAD_SLEEP_STATUS_0_REG_OFFSET, 0xfffffff7u);
  EXPECT_DIF_OK(dif_pinmux_pad_sleep_get_state(
      &dif_pinmux_, /*pad=*/3, kDifPinmuxPadKindMio, &in_sleep_mode));
  EXPECT_FALSE(in_sleep_mode);

  EXPECT_READ32(PINMUX_DIO_PAD_SLEEP_STATUS_REG_OFFSET, 0x00000004u);
  EXPECT_DIF_OK(dif_pinmux_pad_sleep_get_state(
      &dif_pinmux_, /*pad=*/2, kDifPinmuxPadKindDio, &in_sleep_mode));
  EXPECT_TRUE(in_sleep_mode);

  EXPECT_READ32(PINMUX_MIO_PAD_SLEEP_STATUS_0_REG_OFFSET, 0xffff7777u);
  EXPECT_WRITE32(PINMUX_MIO_PAD_SLEEP_STATUS_0_REG_OFFSET, 0xffff7757u);
  EXPECT_DIF_OK(dif_pinmux_pad_sleep_clear_state(&dif_pinmux_, /*pad=*/5,
                                                 kDifPinmuxPadKindMio));
}

TEST_F(PinmuxTest, WakeupConfig) {
  dif_pinmux_wakeup_config_t config = {
      .signal_filter = kDifToggleDisabled,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = 4,
      .mode = kDifPinmuxWakeupModeTimedHigh,
      .counter_threshold = 23,
  };
  EXPECT_READ32(PINMUX_WKUP_DETECTOR_REGWEN_1_REG_OFFSET, 0);
  EXPECT_EQ(dif_pinmux_wakeup_detector_disable(&dif_pinmux_, /*detector=*/1),
            kDifLocked);

  EXPECT_READ32(PINMUX_WKUP_DETECTOR_REGWEN_0_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_pinmux_wakeup_detector_enable(&dif_pinmux_, /*detector=*/0, config),
      kDifLocked);

  EXPECT_READ32(PINMUX_WKUP_DETECTOR_REGWEN_2_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_EN_2_REG_OFFSET, 0);
  EXPECT_DIF_OK(
      dif_pinmux_wakeup_detector_disable(&dif_pinmux_, /*detector=*/2));

  EXPECT_READ32(PINMUX_WKUP_DETECTOR_REGWEN_3_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_EN_3_REG_OFFSET, 0);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_3_REG_OFFSET,
                 {
                     {PINMUX_WKUP_DETECTOR_3_MODE_3_OFFSET,
                      PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_TIMEDHIGH},
                     {PINMUX_WKUP_DETECTOR_3_FILTER_3_BIT, 0},
                     {PINMUX_WKUP_DETECTOR_3_MIODIO_3_BIT, 0},
                 });
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_CNT_TH_3_REG_OFFSET, 23);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_PADSEL_3_REG_OFFSET, 4);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_EN_3_REG_OFFSET, 1);
  EXPECT_DIF_OK(
      dif_pinmux_wakeup_detector_enable(&dif_pinmux_, /*detector=*/3, config));

  config.signal_filter = kDifToggleEnabled;
  config.pad_select = 3;
  config.pad_type = kDifPinmuxPadKindDio;
  config.mode = kDifPinmuxWakeupModeAnyEdge;
  EXPECT_READ32(PINMUX_WKUP_DETECTOR_REGWEN_3_REG_OFFSET, 1);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_EN_3_REG_OFFSET, 0);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_3_REG_OFFSET,
                 {
                     {PINMUX_WKUP_DETECTOR_3_MODE_3_OFFSET,
                      PINMUX_WKUP_DETECTOR_0_MODE_0_VALUE_EDGE},
                     {PINMUX_WKUP_DETECTOR_3_FILTER_3_BIT, 1},
                     {PINMUX_WKUP_DETECTOR_3_MIODIO_3_BIT, 1},
                 });
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_PADSEL_3_REG_OFFSET, 3);
  EXPECT_WRITE32(PINMUX_WKUP_DETECTOR_EN_3_REG_OFFSET, 1);
  EXPECT_DIF_OK(
      dif_pinmux_wakeup_detector_enable(&dif_pinmux_, /*detector=*/3, config));
}

TEST_F(PinmuxTest, WakeupCause) {
  uint32_t detector_map;
  EXPECT_READ32(PINMUX_WKUP_CAUSE_REG_OFFSET, 0x4);
  EXPECT_DIF_OK(dif_pinmux_wakeup_cause_get(&dif_pinmux_, &detector_map));
  EXPECT_EQ(detector_map, 4);

  EXPECT_WRITE32(PINMUX_WKUP_CAUSE_REG_OFFSET, 0x0);
  EXPECT_DIF_OK(dif_pinmux_wakeup_cause_clear(&dif_pinmux_));
}

}  // namespace
}  // namespace dif_pinmux_unittest
