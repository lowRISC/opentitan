// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sensor_ctrl.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "sensor_ctrl_regs.h"  // Generated.

namespace dif_sensor_ctrl_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

class SensorCtrlTest : public Test, public MmioTest {
 protected:
  void SetUp() {
    ASSERT_DIF_OK(dif_sensor_ctrl_init(dev().region(), &sensor_ctrl));
  }

  dif_sensor_ctrl_t sensor_ctrl;
};

TEST_F(SensorCtrlTest, BadArgs) {
  uint32_t good_idx = 0;
  uint32_t bad_idx = SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS + 1;
  dif_toggle_t toggle_arg{};
  dif_sensor_ctrl_events_t events_arg{};
  dif_sensor_ctrl_io_power_status_t power_arg{};

  EXPECT_DIF_BADARG(dif_sensor_ctrl_lock_cfg(nullptr));

  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_set_ast_event_trigger(nullptr, good_idx, toggle_arg));
  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, bad_idx, toggle_arg));

  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_set_alert_fatal(nullptr, good_idx, toggle_arg));
  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, bad_idx, toggle_arg));

  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_recov_events(nullptr, &events_arg));
  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, nullptr));

  EXPECT_DIF_BADARG(dif_sensor_ctrl_clear_recov_event(nullptr, good_idx));
  EXPECT_DIF_BADARG(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, bad_idx));

  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_fatal_events(nullptr, &events_arg));
  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_fatal_events(&sensor_ctrl, nullptr));

  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_get_ast_init_done_status(nullptr, &toggle_arg));
  EXPECT_DIF_BADARG(
      dif_sensor_ctrl_get_ast_init_done_status(&sensor_ctrl, nullptr));

  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_io_power_status(nullptr, &power_arg));
  EXPECT_DIF_BADARG(dif_sensor_ctrl_get_io_power_status(&sensor_ctrl, nullptr));
}

TEST_F(SensorCtrlTest, TriggerEvents) {
  for (size_t i = 0; i < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; i++) {
    EXPECT_READ32(SENSOR_CTRL_ALERT_TRIG_REG_OFFSET, 0);
    EXPECT_WRITE32(SENSOR_CTRL_ALERT_TRIG_REG_OFFSET, 1 << i);
    EXPECT_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, i,
                                                        kDifToggleEnabled));
  }

  for (size_t i = 0; i < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; i++) {
    EXPECT_READ32(SENSOR_CTRL_ALERT_TRIG_REG_OFFSET, -1);
    EXPECT_WRITE32(SENSOR_CTRL_ALERT_TRIG_REG_OFFSET, ~(1 << i));
    EXPECT_DIF_OK(dif_sensor_ctrl_set_ast_event_trigger(&sensor_ctrl, i,
                                                        kDifToggleDisabled));
  }
}

TEST_F(SensorCtrlTest, AlertFatality) {
  for (size_t i = 0; i < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; i++) {
    EXPECT_READ32(SENSOR_CTRL_CFG_REGWEN_REG_OFFSET, 1);
    EXPECT_READ32(SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, 0);
    EXPECT_WRITE32(SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, 1 << i);
    EXPECT_DIF_OK(
        dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, i, kDifToggleEnabled));
  }

  for (size_t i = 0; i < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; i++) {
    EXPECT_READ32(SENSOR_CTRL_CFG_REGWEN_REG_OFFSET, 1);
    EXPECT_READ32(SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, -1);
    EXPECT_WRITE32(SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, ~(1 << i));
    EXPECT_DIF_OK(
        dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, i, kDifToggleDisabled));
  }

  EXPECT_READ32(SENSOR_CTRL_CFG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, 0, kDifToggleDisabled),
      kDifLocked);

  EXPECT_READ32(SENSOR_CTRL_CFG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_sensor_ctrl_set_alert_fatal(&sensor_ctrl, 0, kDifToggleEnabled),
            kDifLocked);
}

TEST_F(SensorCtrlTest, GetRecovEvents) {
  uint32_t events_mask = (1 << SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS) - 1;

  dif_sensor_ctrl_events_t exp_events = 0x987542 & events_mask;
  dif_sensor_ctrl_events_t rcv_events;
  EXPECT_READ32(SENSOR_CTRL_RECOV_ALERT_REG_OFFSET, exp_events);
  EXPECT_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &rcv_events));
  EXPECT_EQ(exp_events, rcv_events);

  exp_events = 0xdc5a8492 & events_mask;
  EXPECT_READ32(SENSOR_CTRL_RECOV_ALERT_REG_OFFSET, exp_events);
  EXPECT_DIF_OK(dif_sensor_ctrl_get_recov_events(&sensor_ctrl, &rcv_events));
  EXPECT_EQ(exp_events, rcv_events);
}

TEST_F(SensorCtrlTest, ClearRecovEvent) {
  for (size_t i = 0; i < SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS; i++) {
    EXPECT_WRITE32(SENSOR_CTRL_RECOV_ALERT_REG_OFFSET, (1 << i));
    EXPECT_DIF_OK(dif_sensor_ctrl_clear_recov_event(&sensor_ctrl, i));
  }
}

TEST_F(SensorCtrlTest, GetFatalEvents) {
  uint32_t events_mask = (1 << SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS) - 1;

  dif_sensor_ctrl_events_t exp_events = 0x1987451 & events_mask;
  dif_sensor_ctrl_events_t rcv_events;
  EXPECT_READ32(SENSOR_CTRL_FATAL_ALERT_REG_OFFSET, exp_events);
  EXPECT_DIF_OK(dif_sensor_ctrl_get_fatal_events(&sensor_ctrl, &rcv_events));
  EXPECT_EQ(exp_events, rcv_events);

  exp_events = 0x9874bac & events_mask;
  EXPECT_READ32(SENSOR_CTRL_FATAL_ALERT_REG_OFFSET, exp_events);
  EXPECT_DIF_OK(dif_sensor_ctrl_get_fatal_events(&sensor_ctrl, &rcv_events));
  EXPECT_EQ(exp_events, rcv_events);
}

TEST_F(SensorCtrlTest, GetAstInitStatus) {
  dif_toggle_t init_done;
  uint32_t exp[4] = {0xa7, 0xa6, 0xbc, 0xf1};
  for (size_t i = 0; i < sizeof(exp) / sizeof(uint32_t); i++) {
    EXPECT_READ32(SENSOR_CTRL_STATUS_REG_OFFSET, exp[i]);
    EXPECT_DIF_OK(
        dif_sensor_ctrl_get_ast_init_done_status(&sensor_ctrl, &init_done));
    EXPECT_EQ(bitfield_bit32_read(exp[i], SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT),
              init_done);
  }
}

TEST_F(SensorCtrlTest, GetIoPowerStatus) {
  dif_sensor_ctrl_io_power_status_t io_power_status;
  uint32_t exp[4] = {0xa7, 0xa0, 0xa3, 0xa5};

  for (size_t i = 0; i < sizeof(exp) / sizeof(uint32_t); i++) {
    EXPECT_READ32(SENSOR_CTRL_STATUS_REG_OFFSET, exp[i]);
    EXPECT_DIF_OK(
        dif_sensor_ctrl_get_io_power_status(&sensor_ctrl, &io_power_status));
    EXPECT_EQ(bitfield_field32_read(exp[i], SENSOR_CTRL_STATUS_IO_POK_FIELD),
              io_power_status);
  }
}

}  // namespace
}  // namespace dif_sensor_ctrl_unittest
