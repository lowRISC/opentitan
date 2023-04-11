// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sensor_ctrl_regs.h"  // Generated.
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

/* In this test, the IO POK status is randomly change by an
 * an external source (user or dv).
 * Only 1 IO change is made at a time.
 * When an IO change is made, an interrupt is triggered and
 * checked by the device. After the interrupt, the status is
 * is checked to ensure only 1 IO change was observed.
 */

static dif_sensor_ctrl_t sensor_ctrl;
static dif_rv_plic_t plic;
static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static sensor_ctrl_isr_ctx_t sensor_ctrl_isr_ctx = {
    .sensor_ctrl = &sensor_ctrl,
    .plic_sensor_ctrl_start_irq_id =
        kTopEarlgreyPlicIrqIdSensorCtrlAonIoStatusChange,
    .expected_irq = kDifSensorCtrlIrqIoStatusChange,
    .is_only_irq = false};

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_sensor_ctrl_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_sensor_ctrl_isr(plic_ctx, sensor_ctrl_isr_ctx, &peripheral,
                                &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralSensorCtrlAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifSensorCtrlIrqIoStatusChange, "IRQ ID: %d is incorrect",
        irq_id);
}

bool test_main(void) {
  uint32_t iterations = 10;
  uint32_t io_mask = (1 << SENSOR_CTRL_PARAM_NUM_IO_RAILS) - 1;
  dif_sensor_ctrl_io_power_status_t last_io_status, curr_io_status;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  // Initialize sensor_ctrl
  CHECK_DIF_OK(dif_sensor_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR),
      &sensor_ctrl));

  // Enable interrupts
  rv_plic_testutils_irq_range_enable(
      &plic, kTopEarlgreyPlicTargetIbex0,
      kTopEarlgreyPlicIrqIdSensorCtrlAonIoStatusChange,
      kTopEarlgreyPlicIrqIdSensorCtrlAonIoStatusChange);

  // Acknowledge the interrupt state that sets by default
  CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge_all(&sensor_ctrl));

  // Enable sensor_ctrl interrupt
  CHECK_DIF_OK(dif_sensor_ctrl_irq_set_enabled(
      &sensor_ctrl, kDifSensorCtrlIrqIoStatusChange, kDifToggleEnabled));

  last_io_status = io_mask;
  for (uint32_t i = 0; i < iterations; ++i) {
    LOG_INFO("Waiting for IO change");
    wait_for_interrupt();
    CHECK_DIF_OK(
        dif_sensor_ctrl_get_io_power_status(&sensor_ctrl, &curr_io_status));
    CHECK(bitfield_popcount32(last_io_status ^ curr_io_status) == 1);
    last_io_status = curr_io_status;
    LOG_INFO("IO change complete");
  }

  return true;
}
