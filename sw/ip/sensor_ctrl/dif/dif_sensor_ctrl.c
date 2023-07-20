// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_sensor_ctrl.h"

#include <assert.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sensor_ctrl_regs.h"  // Generated

/**
 * Helper function to determine if a higher than supported event was supplied
 * as an argument.  This check is used in multiple places so use a helper
 * function.
 */
static inline bool is_ast_event_invalid(dif_sensor_ctrl_event_idx_t event_idx) {
  return event_idx > SENSOR_CTRL_PARAM_NUM_ALERT_EVENTS;
}

/**
 * Helper function to get CFG_REGWEN
 */
static bool is_locked(const dif_sensor_ctrl_t *sensor_ctrl) {
  return (mmio_region_read32(sensor_ctrl->base_addr,
                             SENSOR_CTRL_CFG_REGWEN_REG_OFFSET) == 0);
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_lock_cfg(const dif_sensor_ctrl_t *sensor_ctrl) {
  if (sensor_ctrl == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(sensor_ctrl->base_addr, SENSOR_CTRL_CFG_REGWEN_REG_OFFSET,
                      0);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_set_ast_event_trigger(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_event_idx_t event_idx,
    dif_toggle_t enable) {
  if (sensor_ctrl == NULL || is_ast_event_invalid(event_idx)) {
    return kDifBadArg;
  };

  uint32_t reg = mmio_region_read32(sensor_ctrl->base_addr,
                                    SENSOR_CTRL_ALERT_TRIG_REG_OFFSET);
  reg = bitfield_bit32_write(reg, event_idx, dif_toggle_to_bool(enable));
  mmio_region_write32(sensor_ctrl->base_addr, SENSOR_CTRL_ALERT_TRIG_REG_OFFSET,
                      reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_set_alert_fatal(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_event_idx_t event_idx,
    dif_toggle_t en_fatal) {
  if (sensor_ctrl == NULL || is_ast_event_invalid(event_idx)) {
    return kDifBadArg;
  };

  if (is_locked(sensor_ctrl)) {
    return kDifLocked;
  }

  uint32_t reg = mmio_region_read32(sensor_ctrl->base_addr,
                                    SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET);
  reg = bitfield_bit32_write(reg, event_idx, dif_toggle_to_bool(en_fatal));
  mmio_region_write32(sensor_ctrl->base_addr,
                      SENSOR_CTRL_FATAL_ALERT_EN_REG_OFFSET, reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_recov_events(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_events_t *events) {
  if (sensor_ctrl == NULL || events == NULL) {
    return kDifBadArg;
  };

  *events = mmio_region_read32(sensor_ctrl->base_addr,
                               SENSOR_CTRL_RECOV_ALERT_REG_OFFSET);

  return kDifOk;
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_clear_recov_event(
    const dif_sensor_ctrl_t *sensor_ctrl,
    dif_sensor_ctrl_event_idx_t event_idx) {
  if (sensor_ctrl == NULL || is_ast_event_invalid(event_idx)) {
    return kDifBadArg;
  };

  uint32_t reg = bitfield_bit32_write(0, event_idx, 1);
  mmio_region_write32(sensor_ctrl->base_addr,
                      SENSOR_CTRL_RECOV_ALERT_REG_OFFSET, reg);

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_fatal_events(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_sensor_ctrl_events_t *events) {
  if (sensor_ctrl == NULL || events == NULL) {
    return kDifBadArg;
  };

  *events = mmio_region_read32(sensor_ctrl->base_addr,
                               SENSOR_CTRL_FATAL_ALERT_REG_OFFSET);

  return kDifOk;
};

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_ast_init_done_status(
    const dif_sensor_ctrl_t *sensor_ctrl, dif_toggle_t *done) {
  if (sensor_ctrl == NULL || done == NULL) {
    return kDifBadArg;
  };

  uint32_t reg =
      mmio_region_read32(sensor_ctrl->base_addr, SENSOR_CTRL_STATUS_REG_OFFSET);
  *done = dif_bool_to_toggle(
      bitfield_bit32_read(reg, SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT));

  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_get_io_power_status(
    const dif_sensor_ctrl_t *sensor_ctrl,
    dif_sensor_ctrl_io_power_status_t *io_power_status) {
  if (sensor_ctrl == NULL || io_power_status == NULL) {
    return kDifBadArg;
  };

  uint32_t reg =
      mmio_region_read32(sensor_ctrl->base_addr, SENSOR_CTRL_STATUS_REG_OFFSET);
  *io_power_status =
      bitfield_field32_read(reg, SENSOR_CTRL_STATUS_IO_POK_FIELD);

  return kDifOk;
}
