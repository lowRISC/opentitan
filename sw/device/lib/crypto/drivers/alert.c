// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/alert.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hw/top/alert_handler_regs.h"
#include "hw/top/sensor_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

uint32_t read_alert_registers(void) {
  mmio_region_t sensor_ctrl =
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  mmio_region_t alert_handler =
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);

  // Read the sensors
  uint32_t sensors_recov_alerts =
      mmio_region_read32(sensor_ctrl, SENSOR_CTRL_RECOV_ALERT_REG_OFFSET);
  uint32_t sensors_fatal_alerts =
      mmio_region_read32(sensor_ctrl, SENSOR_CTRL_FATAL_ALERT_REG_OFFSET);
  uint32_t combined_alerts = sensors_recov_alerts | sensors_fatal_alerts;

  // Read out the alerts
  for (uint32_t alert = 0; alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
    uint32_t cause = mmio_region_read32(
        alert_handler, (ptrdiff_t)(alert * sizeof(uint32_t)) +
                           ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET);
    combined_alerts |= cause;
  }
  // Read out the local alerts
  for (uint32_t local_alert = 0; local_alert < ALERT_HANDLER_PARAM_N_LOC_ALERT;
       local_alert++) {
    uint32_t local_cause = mmio_region_read32(
        alert_handler, (ptrdiff_t)(local_alert * sizeof(uint32_t)) +
                           ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET);
    combined_alerts |= local_cause;
  }
  return combined_alerts;
}

status_t init_alert_registers(void) {
  mmio_region_t sensor_ctrl =
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  mmio_region_t alert_handler =
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);

  // Clear the sensors.
  mmio_region_write32(sensor_ctrl, SENSOR_CTRL_RECOV_ALERT_REG_OFFSET,
                      SENSOR_CTRL_RECOV_ALERT_REG_RESVAL);
  mmio_region_write32(sensor_ctrl, SENSOR_CTRL_FATAL_ALERT_REG_OFFSET,
                      SENSOR_CTRL_FATAL_ALERT_REG_RESVAL);
  mmio_region_write32(sensor_ctrl, SENSOR_CTRL_ALERT_TEST_REG_OFFSET,
                      SENSOR_CTRL_ALERT_TEST_REG_RESVAL);
  mmio_region_write32(sensor_ctrl, SENSOR_CTRL_ALERT_TRIG_REG_OFFSET,
                      SENSOR_CTRL_ALERT_TRIG_REG_RESVAL);
  mmio_region_write32(sensor_ctrl, SENSOR_CTRL_INTR_STATE_REG_OFFSET,
                      SENSOR_CTRL_INTR_STATE_REG_RESVAL);

  // Clear the alerts.
  for (uint32_t alert = 0; alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
    mmio_region_write32(alert_handler,
                        (ptrdiff_t)(alert * sizeof(uint32_t)) +
                            ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET,
                        0x1);
  }

  // Clear the local alerts.
  for (uint32_t local_alert = 0; local_alert < ALERT_HANDLER_PARAM_N_LOC_ALERT;
       local_alert++) {
    mmio_region_write32(alert_handler,
                        (ptrdiff_t)(local_alert * sizeof(uint32_t)) +
                            ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET,
                        0x1);
  }

  mmio_region_write32(alert_handler, ALERT_HANDLER_INTR_STATE_REG_OFFSET,
                      0xffffffff);
  return OTCRYPTO_OK;
}
