// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This test checks that SRAMs become inaccessible when an alert is escalated.
 *
 * The device side of this test:
 *
 * 1. Writes to and reads back data from both main and retention SRAM.
 * 2. Configures the alert handlers to lock up the SRAMs for the LC bus
 *    bus integrity alert.
 * 3. Forces that alert.
 *
 * This level of escalation also locks up ibex, so we cannot check the SRAMs
 * from within this test. Instead, a test bench must try to access the SRAMs
 * through the debug module.
 */

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sram_ctrl_regs.h"  // Generated.

static const uint32_t kStatusRegMask = kDifSramCtrlStatusBusIntegErr |
                                       kDifSramCtrlStatusInitErr |
                                       kDifSramCtrlStatusEscalated;

enum {
  kCommandTimeoutMicros = 1 * 1000 * 1000,
};

static dif_alert_handler_t alert_handler;
static dif_lc_ctrl_t lc_ctrl;
static dif_sram_ctrl_t sram_ctrl_main;
static dif_sram_ctrl_t sram_ctrl_ret;

// Buffer to allow the compiler to allocate a safe area in Main SRAM where
// we can do the write/read test without the risk of clobbering data
// used by the program.
OT_SECTION(".data")
static volatile uint32_t sram_buffer_main;

enum test_phase {
  kTestPhaseCfg,
  kTestPhaseEscalate,
};
static volatile uint8_t test_phase = kTestPhaseCfg;

static volatile uintptr_t sram_buffer_addr_main;
static volatile uintptr_t sram_buffer_addr_ret;

/// Write and read back a word of data to check SRAM is responsive.
static bool write_read_data(mmio_region_t sram_region, uint32_t data) {
  mmio_region_write32(sram_region, 0, data);
  uint32_t read_data = mmio_region_read32(sram_region, 0);

  return read_data == data;
}

status_t configure_srams(void) {
  uint32_t base_addr;
  base_addr = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR;
  TRY(dif_sram_ctrl_init(mmio_region_from_addr(base_addr), &sram_ctrl_main));
  base_addr = TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR;
  TRY(dif_sram_ctrl_init(mmio_region_from_addr(base_addr), &sram_ctrl_ret));

  dif_sram_ctrl_status_bitfield_t status_main;
  dif_sram_ctrl_status_bitfield_t status_ret;

  // Check Status registers
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_ret, &status_ret));
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram_ctrl_main, &status_main));

  CHECK((status_main & kStatusRegMask) == 0x0,
        "SRAM main status error bits set, status = %08x.", status_main);
  CHECK((status_ret & kStatusRegMask) == 0x0,
        "SRAM ret status error bits set, status = %08x.", status_ret);

  return OK_STATUS();
}

status_t configure_alert_handler(void) {
  TRY(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));

  dif_alert_handler_escalation_phase_t esc_phases[] = {{
      .phase = kDifAlertHandlerClassStatePhase0,
      .signal = 1,  // This level causes ibex and SRAMs to lock up.
      .duration_cycles = UINT32_MAX,
  }};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 1000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  TRY(dif_alert_handler_configure_alert(
      &alert_handler, kTopEarlgreyAlertIdLcCtrlFatalBusIntegError,
      kDifAlertHandlerClassA, kDifToggleEnabled, kDifToggleEnabled));
  TRY(dif_alert_handler_configure_class(&alert_handler, kDifAlertHandlerClassA,
                                        class_config, kDifToggleEnabled,
                                        kDifToggleEnabled));

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR), &lc_ctrl));

  CHECK_STATUS_OK(configure_alert_handler());
  CHECK_STATUS_OK(configure_srams());

  // Read and Write to/from SRAMs. Main SRAM will use the address of the
  // buffer that has been allocated. Ret SRAM can start at the owner section.
  sram_buffer_addr_main = (uintptr_t)&sram_buffer_main;
  sram_buffer_addr_ret = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
                         offsetof(retention_sram_t, owner);

  mmio_region_t sram_region_main = mmio_region_from_addr(sram_buffer_addr_main);
  mmio_region_t sram_region_ret = mmio_region_from_addr(sram_buffer_addr_ret);

  // Write and read-back some data to both SRAMs to confirm they're responding.
  CHECK(write_read_data(sram_region_main, 0x6b4abfae),
        "main SRAM was not written to/read from correctly");
  CHECK(write_read_data(sram_region_ret, 0x6b4abfae),
        "retention SRAM was not written to/read from correctly");

  OTTF_WAIT_FOR(test_phase == kTestPhaseEscalate, kCommandTimeoutMicros);

  // Trigger an alert in the lifecycle controller.
  CHECK_DIF_OK(
      dif_lc_ctrl_alert_force(&lc_ctrl, kDifLcCtrlAlertFatalBusIntegError));

  // Ibex should have also locked up because of the alert so we don't expect
  // to continue executing.
  LOG_ERROR("Did not expect to execute after alert fired");
  return false;
}
