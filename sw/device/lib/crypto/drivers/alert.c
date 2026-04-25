// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/alert.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "alert_handler_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sensor_ctrl_regs.h"  // Generated.

uint32_t read_alert_registers(void) {
  // Read the sensors
  uint32_t sensors_recov_alerts =
      abs_mmio_read32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                      SENSOR_CTRL_RECOV_ALERT_REG_OFFSET);
  uint32_t sensors_fatal_alerts =
      abs_mmio_read32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                      SENSOR_CTRL_FATAL_ALERT_REG_OFFSET);
  uint32_t combined_alerts = sensors_recov_alerts | sensors_fatal_alerts;

  // Read out the alerts accumulation of the classes
  combined_alerts |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                     ALERT_HANDLER_CLASSA_ACCUM_CNT_REG_OFFSET);
  combined_alerts |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                     ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET);
  combined_alerts |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                     ALERT_HANDLER_CLASSC_ACCUM_CNT_REG_OFFSET);
  combined_alerts |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                     ALERT_HANDLER_CLASSD_ACCUM_CNT_REG_OFFSET);
  // Read out the local alerts
  for (uint32_t local_alert = 0; local_alert < ALERT_HANDLER_PARAM_N_LOC_ALERT;
       local_alert++) {
    uint32_t local_cause =
        abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                        (local_alert * sizeof(uint32_t)) +
                        ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET);
    combined_alerts |= local_cause;
  }
  return combined_alerts;
}

status_t clear_alert_class_accum(void) {
  // Check whether we can write to the class accumulators
  uint32_t regwen = abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                    ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET);
  regwen |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                            ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET);
  regwen |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                            ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET);
  regwen |= abs_mmio_read32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                            ALERT_HANDLER_CLASSD_CLR_REGWEN_REG_OFFSET);
  if ((regwen & 0x1) != 1) {
    return OTCRYPTO_FATAL_ERR;
  }

  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSA_CLR_SHADOWED_REG_OFFSET,
                            1);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSB_CLR_SHADOWED_REG_OFFSET,
                            1);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSC_CLR_SHADOWED_REG_OFFSET,
                            1);
  abs_mmio_write32_shadowed(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                                ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET,
                            1);

  return OTCRYPTO_OK;
}

status_t init_alert_registers(void) {
  // Clear the sensors.
  abs_mmio_write32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                       SENSOR_CTRL_RECOV_ALERT_REG_OFFSET,
                   SENSOR_CTRL_RECOV_ALERT_REG_RESVAL);
  abs_mmio_write32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                       SENSOR_CTRL_FATAL_ALERT_REG_OFFSET,
                   SENSOR_CTRL_FATAL_ALERT_REG_RESVAL);
  abs_mmio_write32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                       SENSOR_CTRL_ALERT_TEST_REG_OFFSET,
                   SENSOR_CTRL_ALERT_TEST_REG_RESVAL);
  abs_mmio_write32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                       SENSOR_CTRL_ALERT_TRIG_REG_OFFSET,
                   SENSOR_CTRL_ALERT_TRIG_REG_RESVAL);
  abs_mmio_write32(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR +
                       SENSOR_CTRL_INTR_STATE_REG_OFFSET,
                   SENSOR_CTRL_INTR_STATE_REG_RESVAL);

  // Clear the alerts.
  for (uint32_t alert = 0; alert < ALERT_HANDLER_PARAM_N_ALERTS; alert++) {
    abs_mmio_write32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                         (alert * sizeof(uint32_t)) +
                         ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET,
                     0x1);
  }

  // Clear the local alerts.
  for (uint32_t local_alert = 0; local_alert < ALERT_HANDLER_PARAM_N_LOC_ALERT;
       local_alert++) {
    abs_mmio_write32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                         (local_alert * sizeof(uint32_t)) +
                         ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET,
                     0x1);
  }

  // Clear the interupt states.
  abs_mmio_write32(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR +
                       ALERT_HANDLER_INTR_STATE_REG_OFFSET,
                   0xffffffff);

  // Clear the class accumulators.
  return clear_alert_class_accum();
}
