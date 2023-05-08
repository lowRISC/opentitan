// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "aes_regs.h"
#include "alert_handler_regs.h"
#include "hmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"
#include "kmac_regs.h"
#include "otbn_regs.h"
#include "spi_host_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"
#include "usbdev_regs.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_rv_plic_t plic;
static dif_alert_handler_t alert_handler;
static dif_clkmgr_t clkmgr;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;
static dif_usbdev_t usbdev;
static dif_aes_t aes;
static dif_hmac_t hmac;
static dif_kmac_t kmac;
static dif_otbn_t otbn;
static dif_rstmgr_t rstmgr;
static dif_flash_ctrl_state_t flash_ctrl;

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic,
    .hart_id = kPlicTarget,
};

/**
 * Depends on the clock domain, sometimes alert handler will trigger a spurious
 * alert after the alert timeout. (Issue #2321)
 * So we allow class A interrupt to fire after the real timeout interrupt is
 * triggered.
 */
static alert_handler_isr_ctx_t alert_handler_ctx = {
    .alert_handler = &alert_handler,
    .plic_alert_handler_start_irq_id = kTopEarlgreyPlicIrqIdAlertHandlerClassa,
    .expected_irq = kDifAlertHandlerIrqClassb,
    .is_only_irq = false,
};

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host0));

  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR), &spi_host1));

  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));

  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));

  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));

  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Initialize flash_ctrl
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

// List of alerts
static const uint32_t aes_alerts[] = {kTopEarlgreyAlertIdAesFatalFault,
                                      kTopEarlgreyAlertIdAesRecovCtrlUpdateErr};
static const uint32_t hmac_alerts[] = {kTopEarlgreyAlertIdHmacFatalFault};
static const uint32_t kmac_alerts[] = {
    kTopEarlgreyAlertIdKmacFatalFaultErr,
    kTopEarlgreyAlertIdKmacRecovOperationErr};
static const uint32_t otbn_alerts[] = {kTopEarlgreyAlertIdOtbnFatal,
                                       kTopEarlgreyAlertIdOtbnRecov};
static const uint32_t spihost0_alerts[] = {
    kTopEarlgreyAlertIdSpiHost0FatalFault};
static const uint32_t spihost1_alerts[] = {
    kTopEarlgreyAlertIdSpiHost1FatalFault};
static const uint32_t usbdev_alerts[] = {kTopEarlgreyAlertIdUsbdevFatalFault};

static const uint32_t num_aes_alerts = ARRAYSIZE(aes_alerts);
static const uint32_t num_hmac_alerts = ARRAYSIZE(hmac_alerts);
static const uint32_t num_kmac_alerts = ARRAYSIZE(kmac_alerts);
static const uint32_t num_otbn_alerts = ARRAYSIZE(otbn_alerts);
static const uint32_t num_spihost0_alerts = ARRAYSIZE(spihost0_alerts);
static const uint32_t num_spihost1_alerts = ARRAYSIZE(spihost1_alerts);
static const uint32_t num_usbdev_alerts = ARRAYSIZE(usbdev_alerts);

static const size_t num_alerts =
    ARRAYSIZE(aes_alerts) + ARRAYSIZE(hmac_alerts) + ARRAYSIZE(kmac_alerts) +
    ARRAYSIZE(otbn_alerts) + ARRAYSIZE(spihost0_alerts) +
    ARRAYSIZE(spihost1_alerts) + ARRAYSIZE(usbdev_alerts);

/**
 * A structure to keep the info for peripheral IPs
 */
typedef struct test {
  /**
   * Name of the peripheral.
   */
  const char *name;
  /**
   * Base address for the peripheral.
   */
  uintptr_t base;
  /**
   * Offset to the peripheral's ALERT_TEST register.
   */
  ptrdiff_t offset;
  /**
   * Handle to the DIF object for this peripheral.
   */
  void *dif;
  /**
   * The fatal_alert pin in peripheral's ALERT_TEST reg
   */
  uint32_t fatal_alert_bit;
  /**
   * List of Alert IDs for the peripheral
   */
  const uint32_t *alert_ids;
  /**
   * number of alerts for the peripheral
   */
  const uint32_t num_alert_peri;
  /**
   * The index of this device's clk in the clock manager.
   */
  uint32_t clk_index;
  /**
   * Is the clock hinteable (==true) or gateable(==false).
   */
  bool is_hintable;
} test_t;

// The array of the peripherals
static const test_t kPeripherals[] = {
    // Hintable clock IPS
    {
        .name = "AES",
        .base = TOP_EARLGREY_AES_BASE_ADDR,
        .offset = AES_ALERT_TEST_REG_OFFSET,
        .dif = &aes,
        .fatal_alert_bit = kDifAesAlertFatalFault,
        .alert_ids = aes_alerts,
        .num_alert_peri = num_aes_alerts,
        .clk_index = kTopEarlgreyHintableClocksMainAes,
        .is_hintable = true,
    },
    {
        .name = "HMAC",
        .base = TOP_EARLGREY_HMAC_BASE_ADDR,
        .offset = HMAC_ALERT_TEST_REG_OFFSET,
        .dif = &hmac,
        .fatal_alert_bit = kDifHmacAlertFatalFault,
        .alert_ids = hmac_alerts,
        .num_alert_peri = num_hmac_alerts,
        .clk_index = kTopEarlgreyHintableClocksMainHmac,
        .is_hintable = true,
    },
    {
        .name = "KMAC",
        .base = TOP_EARLGREY_KMAC_BASE_ADDR,
        .offset = KMAC_ALERT_TEST_REG_OFFSET,
        .dif = &kmac,
        .fatal_alert_bit = kDifKmacAlertFatalFault,
        .alert_ids = kmac_alerts,
        .num_alert_peri = num_kmac_alerts,
        .clk_index = kTopEarlgreyHintableClocksMainKmac,
        .is_hintable = true,
    },
    {
        .name = "OTBN",
        .base = TOP_EARLGREY_OTBN_BASE_ADDR,
        .offset = OTBN_ALERT_TEST_REG_OFFSET,
        .dif = &otbn,
        .fatal_alert_bit = kDifOtbnAlertFatal,
        .alert_ids = otbn_alerts,
        .num_alert_peri = num_otbn_alerts,
        .clk_index = kTopEarlgreyHintableClocksMainOtbn,
        .is_hintable = true,
    },
    // Gateable clock IPs
    {
        .name = "SPI_HOST0",
        .base = TOP_EARLGREY_SPI_HOST0_BASE_ADDR,
        .offset = SPI_HOST_ALERT_TEST_REG_OFFSET,
        .dif = &spi_host0,
        .fatal_alert_bit = 0,
        .alert_ids = spihost0_alerts,
        .num_alert_peri = num_spihost0_alerts,
        .clk_index = kTopEarlgreyGateableClocksIoPeri,
        .is_hintable = false,
    },
    {
        .name = "SPI_HOST1",
        .base = TOP_EARLGREY_SPI_HOST1_BASE_ADDR,
        .offset = SPI_HOST_ALERT_TEST_REG_OFFSET,
        .dif = &spi_host1,
        .fatal_alert_bit = 0,
        .alert_ids = spihost1_alerts,
        .num_alert_peri = num_spihost1_alerts,
        .clk_index = kTopEarlgreyGateableClocksIoDiv2Peri,
        .is_hintable = false,
    },
    {
        .name = "USB",
        .base = TOP_EARLGREY_USBDEV_BASE_ADDR,
        .offset = USBDEV_ALERT_TEST_REG_OFFSET,
        .dif = &usbdev,
        .fatal_alert_bit = 0,
        .alert_ids = usbdev_alerts,
        .num_alert_peri = num_usbdev_alerts,
        .clk_index = kTopEarlgreyGateableClocksUsbPeri,
        .is_hintable = false,
    },
};

/**
 * Configure and enable alerts of `num_peripheral` peripherals starting from the
 * `first_peripheral`.
 * @param num_peripherals The number of peripherals, of which alerts will be
 * enabled
 * @param first_peripheral The address of the first peripheral in the range
 * @param ping_timeout The timeout value for the ping timer object.
 */
static void alert_handler_config_peripherals(uint32_t num_peripherals,
                                             const test_t *first_peripheral,
                                             uint32_t ping_timeout) {
  dif_alert_handler_alert_t alerts[num_alerts];
  dif_alert_handler_class_t alert_classes[num_alerts];

  // Enable all alerts coming from the chosen peripherals
  // Configure them as Class A.
  size_t array_idx = 0;
  test_t *peri_ptr;
  for (int ii = 0; ii < num_peripherals; ii++) {
    peri_ptr = (test_t *)first_peripheral + ii;
    for (int jj = 0; jj < peri_ptr->num_alert_peri; jj++) {
      alerts[array_idx] = peri_ptr->alert_ids[jj];
      alert_classes[array_idx] = kDifAlertHandlerClassA;
      array_idx++;
    }
  }

  // Enable the alert_ping_fail local alert and configure that as Class B.
  dif_alert_handler_local_alert_t loc_alerts[] = {
      kDifAlertHandlerLocalAlertAlertPingFail};
  dif_alert_handler_class_t loc_alert_classes[] = {kDifAlertHandlerClassB};

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase0,
       .signal = 0,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 10000,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
  };

  dif_alert_handler_class_config_t class_configs[] = {class_config,
                                                      class_config};

  dif_alert_handler_class_t classes[] = {kDifAlertHandlerClassA,
                                         kDifAlertHandlerClassB};
  dif_alert_handler_config_t config = {
      .alerts = alerts,
      .alert_classes = alert_classes,
      .alerts_len = array_idx,
      .local_alerts = loc_alerts,
      .local_alert_classes = loc_alert_classes,
      .local_alerts_len = ARRAYSIZE(loc_alerts),
      .classes = classes,
      .class_configs = class_configs,
      .classes_len = ARRAYSIZE(class_configs),
      .ping_timeout = ping_timeout,
  };

  CHECK_STATUS_OK(alert_handler_testutils_configure_all(&alert_handler, config,
                                                        kDifToggleEnabled));
  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
}

/**
 *  A utility function to enable/disable hintable and gateable clocks
 */
void set_peripheral_clock(const test_t *peripheral,
                          dif_toggle_t new_clk_state) {
  dif_toggle_t clk_state;
  if (peripheral->is_hintable) {
    // Set the new clock state
    CHECK_DIF_OK(dif_clkmgr_hintable_clock_set_hint(
        &clkmgr, peripheral->clk_index, new_clk_state));
    // Verify the new clock state
    CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(
        &clkmgr, peripheral->clk_index, &clk_state));
    CHECK(clk_state == new_clk_state,
          "intended_clk_state = %d, received_clk_state = %d", new_clk_state,
          clk_state);

  } else {
    CHECK_DIF_OK(dif_clkmgr_gateable_clock_set_enabled(
        &clkmgr, peripheral->clk_index, new_clk_state));
    // Verify the new clock state
    CHECK_DIF_OK(dif_clkmgr_gateable_clock_get_enabled(
        &clkmgr, peripheral->clk_index, &clk_state));
    CHECK(clk_state == new_clk_state,
          "intended_clk_state = %d, received_clk_state = %d", new_clk_state,
          clk_state);
  }
};

/**
 * A utility function to wait enough until the alert handler pings a peripheral
 * alert
 */
void wait_enough_for_alert_ping() {
  // wait enough
  if (kDeviceType == kDeviceFpgaCw310) {
    // NUM_ALERTS*2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // (2**6)*2*4*(2**16)*(400ns) = 12.8s
    busy_spin_micros(1000 * 12800);
  } else if (kDeviceType == kDeviceSimDV) {
    // NUM_ALERTS*2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // (2**6)*2*4*(2**3)*(40ns) = 160us
    busy_spin_micros(160);
  } else {
    // Verilator
    // NUM_ALERTS*2*margin_of_safety*(2**DW)*(1/kClockFreqPeripheralHz)
    // (2**6)*2*4*(2**16)*(8us) = 256s
    // This seems to be impractical for the current clock frequency config
    // of the Verilator tests (kClockFreqPeripheralHz = 125K).
    LOG_FATAL("SUPPORTED PLATFORMS: DV and FPGA");
    LOG_FATAL("TO SUPPORT THE PLATFORM %d, COMPUTE THE RIGHT WAIT-TIME",
              kDeviceType);
  }
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral_serviced;
  dif_alert_handler_irq_t irq_serviced;
  isr_testutils_alert_handler_isr(plic_ctx, alert_handler_ctx,
                                  &peripheral_serviced, &irq_serviced);
  CHECK(peripheral_serviced == kTopEarlgreyPlicPeripheralAlertHandler,
        "Interurpt from unexpected peripheral: %d", peripheral_serviced);
}

enum {
  // Non-volatile counter for the test steps on FPGA.
  kCounterTestSteps = 0,
};

// This function will run after every device reset
bool test_main(void) {
  init_peripherals();

  // A generic loop variable
  int ii;
  // To keep the test results
  bool is_cause;

  // The test consists of multiple test phases
  // Each test phase consists of ARRAYSIZE(kPeripherals) steps
  // At every step, a specific peripheral is tested
  size_t test_phase;
  size_t test_step_cnt;
  size_t peri_idx;

  // Need a NVM counter to keep the test-step info
  // between resets on the FPGA.
  if (kDeviceType == kDeviceFpgaCw310) {
    // Enable flash access
    CHECK_STATUS_OK(
        flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                   /*rd_en*/ true,
                                                   /*prog_en*/ true,
                                                   /*erase_en*/ true,
                                                   /*scramble_en*/ false,
                                                   /*ecc_en*/ false,
                                                   /*he_en*/ false));

    CHECK_STATUS_OK(
        flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));
    if (test_step_cnt == 256) {
      CHECK_STATUS_OK(flash_ctrl_testutils_counter_init_zero(
          &flash_ctrl, kCounterTestSteps));
      CHECK_STATUS_OK(
          flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));
    }
  } else {
    // Initialize the test_step counter to zero for the simulation
    test_step_cnt = 0;
  }

  /* TEST PHASE #0: NEGATIVE TESTING (FPGA-ONLY)

    The timeout value is set to 2
    All of the alerts should trigger ping_timeout_alert
    if they are not clock_gated
    TEST: for_each_peripheral
      1- Disable the clock
      2- Enable the corresponding alerts
      3- Wait long enough
      4- Confirm that ping_timeout has not been triggered
      5- Reset the device to test the next peripheral
  */
  while (test_step_cnt < 1 * ARRAYSIZE(kPeripherals)) {
    // Run the negative test only on the FPGA
    // This will save the test time in the simulation
    if (kDeviceType == kDeviceFpgaCw310) {
      // Read the test_step_cnt and compute the test phase
      // amd the peripheral ID to test
      CHECK_STATUS_OK(
          flash_ctrl_testutils_counter_get(kCounterTestSteps, &test_step_cnt));
      test_phase = test_step_cnt / ARRAYSIZE(kPeripherals);
      peri_idx = test_step_cnt - (test_phase)*ARRAYSIZE(kPeripherals);

      // Wait for a random time <= 1024us
      busy_spin_micros(rand_testutils_gen32_range(1, 1024));

      // Disable the clock of the peripheral
      set_peripheral_clock(&kPeripherals[peri_idx], kDifToggleDisabled);

      alert_handler_config_peripherals(
          /*num_peripherals*/ 1, /* *first_peripheral*/ &kPeripherals[peri_idx],
          /*ping_timeout*/ 2);

      // wait enough until the alert handler pings the peripheral
      wait_enough_for_alert_ping();

      // Check the ping_timeout alert status
      CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
          &alert_handler, kDifAlertHandlerLocalAlertAlertPingFail, &is_cause));
      CHECK(!is_cause,
            "Expected response is ping_timeout_fail= 0! But we got "
            "ping_timrout_fail = 1 for peripheral[%d]",
            peri_idx);

      // Enable the clock again
      set_peripheral_clock(&kPeripherals[peri_idx], kDifToggleEnabled);

      // Increment the test_step counter
      CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(
          &flash_ctrl, kCounterTestSteps));
      // Request system reset to unlock the alert handler config and test the
      // next peripheral
      CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    } else {
      // For the simulation, only increment the test_step counter
      // to procced to the next phase without resetting the device
      test_step_cnt++;
    }
  }

  /* TEST PHASE #1: TEST THE REGULAR CONFIG

    The timeout value is set to 256
    None of the alerts should trigger ping_timeout_alert
    TEST:
    enable_alerts (all_peripherals, timeout=256)
    for_each_peripheral
      1- wait for random time
      2- Disable the peripheral's clock
      3- Wait long enough
      4- Confirm that ping_timeout has not been triggered
  */

  // Enable and lock the all peripherals' alerts at the beginning of the PHASE
  // #1
  if (test_step_cnt == 1 * ARRAYSIZE(kPeripherals)) {
    alert_handler_config_peripherals(
        /*num_peripherals*/ ARRAYSIZE(kPeripherals),
        /* *first_peripheral*/ &kPeripherals[0], /*ping_timeout*/ 256);
  }

  while (test_step_cnt < 2 * ARRAYSIZE(kPeripherals)) {
    // Read the test_step_cnt and compute the test phase
    // amd the peripheral ID to test
    test_phase = test_step_cnt / ARRAYSIZE(kPeripherals);
    peri_idx = test_step_cnt - (test_phase)*ARRAYSIZE(kPeripherals);

    // Wait for a random time <= 1024us
    busy_spin_micros(rand_testutils_gen32_range(1, 1024));

    // Disable the clock of the peripheral
    set_peripheral_clock(&kPeripherals[peri_idx], kDifToggleDisabled);

    // wait enough until the alert handler pings the peripheral
    wait_enough_for_alert_ping();

    // Check the alert status
    CHECK_DIF_OK(dif_alert_handler_local_alert_is_cause(
        &alert_handler, kDifAlertHandlerLocalAlertAlertPingFail, &is_cause));
    CHECK(!is_cause, "Expected response: No alert_ping_fail! but we got %d",
          is_cause);

    // Enable the clock of the peripheral again
    set_peripheral_clock(&kPeripherals[peri_idx], kDifToggleEnabled);

    // Increment the test counter
    test_step_cnt++;
  }

  return true;
}
