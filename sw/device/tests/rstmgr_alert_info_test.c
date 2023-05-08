// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "alert_handler_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
/*
  RSTMGR ALERT_INFO Test

  This test runs some alert / dump scenario and check integrity of
  ALERT_INFO coming from alert_hander to rstmgr.

  From dif_rstmgr_reset_info_t, there are 8 different resets.
  This test covers 3 of those (kDifRstmgrResetInfoSw,
  kDifRstmgrResetInfoWatchdog, kDifRstmgrResetInfoEscalation).
  kDifRstmgrResetInfoNdm will be added as a separate test after ndm request test
  is available. Test goes for 3 rounds, and on each round it creates a different
  reset scenario.

  Round 1: Single Class profile
  - Trigger alert from i2c0..2 by calling alert_force.
  - This will trigger kDifAlertHandlerIrqClassa from alert_handler.
  - Also alert_info start to transfer from alert_handler to rstmgr.
  - Upon detecting interrupt, 'ottf_external_isr' request reset to rstmgr
  - After reset, alert_info will be available at rstmgr.
  - Read alert_info from rstmgr and compare with expected value.

  Round 2: Multi Classes profile
  - Trigger alert from uart0..3 and otp_ctrl.
  - Setup the aon_timer wdog bark and bite timeouts.
  - Let the timer expire to create watchdog bite.
  - After reset, coalesced alert info from uarts and otp_ctrl
    will be available from rstmgr.
  - Read alert_info from rstmgr and compare with expected value.

  Round 3: All Classes profile with alert escalation
  - Trigger rv_core_ibex alert that leads to an interrupt.
  - Trigger other alerts for all classes.
  - rv_core_ibex alert will be escalated to phase2 then it will trigger
    reset.
  - Read alert_info from rstmgr and compare with expected value.

  Round 4: Local alert
  - Trigger local alert by setting ping timeout value to 1.
  - Once alert triggers interrupt, call sw_device reset from interrupt
    handler.
  - After reset, read alert_info from rstmgr and compare with expected value.

 */

OTTF_DEFINE_TEST_CONFIG();

enum {
  kWdogBarkMicros = 200,          // us
  kWdogBiteMicros = 200,          // us
  kEscalationPhase0Micros = 300,  // us
  kEscalationPhase1Micros = 200,  // us
  kEscalationPhase2Micros = 100,  // us
  kRoundOneDelay = 100,           // us
  kRoundTwoDelay = 100,           // us
  kRoundThreeDelay = 1000         // us
};

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_flash_ctrl_state_t flash_ctrl;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_uart_t uart0, uart1, uart2, uart3;
static dif_otp_ctrl_t otp_ctrl;
static dif_spi_host_t spi_host;
static dif_rv_plic_t plic;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_i2c_t i2c0, i2c1, i2c2;

typedef struct node {
  const char *name;
  dif_alert_handler_alert_t alert;
  dif_alert_handler_class_t class;
} node_t;

typedef enum test_round {
  kRound1 = 0,
  kRound2 = 1,
  kRound3 = 2,
  kRound4 = 3,
  kRoundTotal = 4
} test_round_t;

static volatile test_round_t global_test_round;
static volatile uint32_t global_alert_called;
static const dif_alert_handler_escalation_phase_t
    kEscProfiles[][ALERT_HANDLER_PARAM_N_CLASSES] = {
        [kDifAlertHandlerClassA] = {{.phase = kDifAlertHandlerClassStatePhase0,
                                     .signal = 0,
                                     .duration_cycles = 5000},
                                    {.phase = kDifAlertHandlerClassStatePhase1,
                                     .signal = 0,
                                     .duration_cycles = 3000}},
        [kDifAlertHandlerClassB] = {{.phase = kDifAlertHandlerClassStatePhase1,
                                     .signal = 0,
                                     .duration_cycles = 3000}},
        [kDifAlertHandlerClassC] = {{.phase = kDifAlertHandlerClassStatePhase0,
                                     .signal = 0,
                                     .duration_cycles = 5000},
                                    {.phase = kDifAlertHandlerClassStatePhase1,
                                     .signal = 0,
                                     .duration_cycles = 3000}},
        [kDifAlertHandlerClassD] = {{.phase = kDifAlertHandlerClassStatePhase0,
                                     .signal = 0,
                                     .duration_cycles = 7200},
                                    {.phase = kDifAlertHandlerClassStatePhase1,
                                     .signal = 1,
                                     .duration_cycles = 4800},
                                    {.phase = kDifAlertHandlerClassStatePhase2,
                                     .signal = 3,
                                     .duration_cycles = 2400}}};

static const dif_alert_handler_class_config_t
    kConfigProfiles[ALERT_HANDLER_PARAM_N_CLASSES] = {
        [kDifAlertHandlerClassA] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = kEscProfiles[kDifAlertHandlerClassA],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassB] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = kEscProfiles[kDifAlertHandlerClassB],
                .escalation_phases_len = 1,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassC] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = kEscProfiles[kDifAlertHandlerClassC],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassD] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 1000,
                .escalation_phases = kEscProfiles[kDifAlertHandlerClassD],
                .escalation_phases_len = 3,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
            },
};

typedef struct test_alert_info {
  char *test_name;
  alert_handler_testutils_info_t alert_info;
} test_alert_info_t;

static test_alert_info_t kExpectedInfo[kRoundTotal] = {
    [kRound1] =
        {
            .test_name = "Single class(ClassA)",
            .alert_info =
                {
                    .class_accum_cnt = {3, 0, 0, 0},
                    .class_esc_state = {kCstatePhase0, kCstateIdle, kCstateIdle,
                                        kCstateIdle},
                },
        },
    [kRound2] =
        {
            .test_name = "Multi classes(ClassB,C)",
            .alert_info =
                {
                    .class_accum_cnt = {0, 1, 4, 0},
                    .class_esc_state = {kCstateIdle, kCstatePhase1,
                                        kCstatePhase0, kCstateIdle},
                },
        },
    [kRound3] =
        {
            .test_name = "All classes",
            .alert_info =
                {
                    .class_accum_cnt = {1, 1, 1, 1},
                    .class_esc_state = {kCstatePhase0, kCstatePhase1,
                                        kCstatePhase0, kCstatePhase0},
                },
        },
    [kRound4] =
        {
            .test_name = "Local alert(ClassB)",
            .alert_info =
                {
                    .loc_alert_cause =
                        (0x1 << kDifAlertHandlerLocalAlertAlertPingFail),
                    .class_accum_cnt = {0, 1, 0, 0},
                    .class_esc_state = {kCstateIdle, kCstatePhase2, kCstateIdle,
                                        kCstateIdle},
                },
        },
};

static node_t test_node[kTopEarlgreyAlertPeripheralLast];

static void set_extra_alert(volatile uint32_t *set) {
  CHECK_DIF_OK(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault));
  CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
  CHECK_DIF_OK(dif_spi_host_alert_force(&spi_host, kDifSpiHostAlertFatalFault));
  *set = 1;
}

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral;
  dif_rv_plic_irq_id_t irq_id;
  uint32_t irq = 0;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq =
        (dif_aon_timer_irq_t)(irq_id -
                              (dif_rv_plic_irq_id_t)
                                  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    irq = (irq_id -
           (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);

    switch (irq) {
      case 0:  // class a
        LOG_INFO("IRQ: class A");
        CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
            &alert_handler, kDifI2cAlertFatalFault));

        // check classes
        dif_alert_handler_class_state_t state;
        CHECK_DIF_OK(dif_alert_handler_get_class_state(
            &alert_handler, kDifAlertHandlerClassA, &state));

        // sw reset for round 1
        if (global_test_round == kRound1) {
          CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
        }
        CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));

        break;
      case 1:
        LOG_INFO("IRQ: class B %d", global_test_round);
        break;
      case 2:
        LOG_INFO("IRQ: class C");
        break;
      case 3:
        if (global_alert_called == 0) {
          set_extra_alert(&global_alert_called);
          LOG_INFO("IRQ: class D");
          LOG_INFO("IRQ: extra alert called");
        }
        break;
      default:
        LOG_FATAL("IRQ: unknown irq %d", irq);
    }
  }
  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.

  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, irq_id));
}

static void print_alert_cause(alert_handler_testutils_info_t info) {
  for (uint32_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    LOG_INFO("alert_cause[%d]: 0x%x", i, info.alert_cause[i]);
  }
}

/*
 * Configure alert for i2c0..i2c2 s.t.
 * .alert class = class A
 * .escalation phase0,1
 * .disable ping timer
 */
static void prgm_alert_handler_round1(void) {
  dif_alert_handler_class_t alert_class = kDifAlertHandlerClassA;

  for (int i = kTopEarlgreyAlertPeripheralI2c0;
       i < kTopEarlgreyAlertPeripheralI2c2 + 1; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, test_node[i].alert, test_node[i].class,
        /*enabled=*/kDifToggleEnabled, /*locked=*/kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_alert_handler_configure_class(
      &alert_handler, alert_class, kConfigProfiles[alert_class],
      /*enabled=*/kDifToggleEnabled, /*locked=*/kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 0, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));
}

/*
 * Configure alert for uart0..3
 * .alert class = class C
 * .escalation phase0,1
 * Configure alert from aon timer
 * .alert class = class B
 * .escalation phases 1
 *
 * Set esc_phases.signal = 0 for all cases to avoid
 * watchdog timer freeze.
 */
static void prgm_alert_handler_round2(void) {
  dif_alert_handler_class_t alert_classes[] = {kDifAlertHandlerClassC,
                                               kDifAlertHandlerClassB};
  dif_alert_handler_class_config_t class_configs[] = {
      kConfigProfiles[kDifAlertHandlerClassC],
      kConfigProfiles[kDifAlertHandlerClassB]};

  for (int i = kTopEarlgreyAlertPeripheralUart0;
       i < kTopEarlgreyAlertPeripheralUart3 + 1; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, test_node[i].alert, test_node[i].class,
        /*enabled=*/kDifToggleEnabled, /*locked=*/kDifToggleEnabled));
  }
  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, test_node[kTopEarlgreyAlertPeripheralOtpCtrl].alert,
      test_node[kTopEarlgreyAlertPeripheralOtpCtrl].class,
      /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  for (int i = 0; i < ARRAYSIZE(alert_classes); ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_classes[i], class_configs[i],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }
}

/*
 * Set I2c0 alert to class a
 *     spi_host alert to class b
 *     uart0 alert to class c and
 *     the rest to class d
 *
 * For class d, enable 3 phases and escalation reset will be
 * triggered at phase2
 */

static void prgm_alert_handler_round3(void) {
  // Enable all incoming alerts. This will create ping timeout event
  // for all possible alerts and will see the timeout more often.
  dif_alert_handler_class_t alert_class;

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    if (i == kTopEarlgreyAlertIdSpiHost0FatalFault) {
      alert_class = kDifAlertHandlerClassB;
    } else if (i == kTopEarlgreyAlertIdUart0FatalFault) {
      alert_class = kDifAlertHandlerClassC;
    } else if (i == kTopEarlgreyAlertIdI2c0FatalFault) {
      alert_class = kDifAlertHandlerClassA;
    } else {
      alert_class = kDifAlertHandlerClassD;
    }
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, i, alert_class, /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }

  dif_alert_handler_class_t alert_classes[] = {
      kDifAlertHandlerClassA, kDifAlertHandlerClassB, kDifAlertHandlerClassC,
      kDifAlertHandlerClassD};

  dif_alert_handler_class_config_t class_d_config =
      kConfigProfiles[kDifAlertHandlerClassD];

  dif_alert_handler_escalation_phase_t class_d_esc[3];

  if (kDeviceType == kDeviceFpgaCw310) {
    uint32_t cpu_freq = kClockFreqCpuHz;
    uint32_t peri_freq = kClockFreqPeripheralHz;
    uint32_t cycles = kUartTxFifoCpuCycles * (cpu_freq / peri_freq);
    class_d_esc[0] = kEscProfiles[kDifAlertHandlerClassD][0];
    class_d_esc[1] = kEscProfiles[kDifAlertHandlerClassD][1];
    class_d_esc[2] = kEscProfiles[kDifAlertHandlerClassD][2];
    // we must allow sufficient time for the device to complete uart
    class_d_esc[0].duration_cycles = cycles;
    class_d_config.escalation_phases = class_d_esc;
  }

  LOG_INFO("Escalation set to %d cycles",
           class_d_config.escalation_phases[0].duration_cycles);

  dif_alert_handler_class_config_t class_configs[] = {
      kConfigProfiles[kDifAlertHandlerClassA],
      kConfigProfiles[kDifAlertHandlerClassB],
      kConfigProfiles[kDifAlertHandlerClassC], class_d_config};

  for (int i = 0; i < ARRAYSIZE(alert_classes); ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_classes[i], class_configs[i],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 1000, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_core_ibex_alert_force(&rv_core_ibex,
                                            kDifRvCoreIbexAlertRecovSwErr));
}

/*
 * Configure all global alert enable and mapped to class A
 * Configure local alert enable and mapped to class B
 * For class B, set signal to 3 to trigger escalation reset
 * Change ping timeout value to 1 to cause alert ping timeout
 */

static void prgm_alert_handler_round4(void) {
  dif_alert_handler_alert_t alerts[ALERT_HANDLER_PARAM_N_ALERTS];
  dif_alert_handler_class_t alert_classes[ALERT_HANDLER_PARAM_N_ALERTS];

  // Enable all alerts to enable ping associate with them.
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, i, kDifAlertHandlerClassA, kDifToggleEnabled,
        kDifToggleEnabled));
  }

  // Enable alert ping fail local alert and configure that to classb.
  dif_alert_handler_local_alert_t loc_alert =
      kDifAlertHandlerLocalAlertAlertPingFail;
  dif_alert_handler_class_t loc_alert_class = kDifAlertHandlerClassB;

  dif_alert_handler_escalation_phase_t esc_phases[] = {
      {.phase = kDifAlertHandlerClassStatePhase2,
       .signal = 3,
       .duration_cycles = 2000}};

  dif_alert_handler_class_config_t class_config = {
      .auto_lock_accumulation_counter = kDifToggleDisabled,
      .accumulator_threshold = 0,
      .irq_deadline_cycles = 240,
      .escalation_phases = esc_phases,
      .escalation_phases_len = ARRAYSIZE(esc_phases),
      .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
  };

  CHECK_DIF_OK(dif_alert_handler_configure_local_alert(
      &alert_handler, loc_alert, loc_alert_class, kDifToggleEnabled,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_configure_class(
      &alert_handler, kDifAlertHandlerClassB, class_config, kDifToggleEnabled,
      kDifToggleEnabled));

  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 1, kDifToggleEnabled, kDifToggleEnabled));

  // Enables alert handler irq.
  CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
      &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
}

static void peripheral_init(void) {
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR), &i2c0));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR), &i2c1));
  CHECK_DIF_OK(
      dif_i2c_init(mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR), &i2c2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR), &uart1));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR), &uart2));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR), &uart3));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Set pwrmgr reset_en
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
}

static void collect_alert_dump_and_compare(test_round_t round) {
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  size_t seg_size;
  alert_handler_testutils_info_t actual_info;

  CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr, dump, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &seg_size));

  LOG_INFO("Testname: %s  DUMP SIZE %d", kExpectedInfo[round].test_name,
           seg_size);
  for (int i = 0; i < seg_size; i++) {
    LOG_INFO("DUMP:%d: 0x%x", i, dump[i]);
  }

  CHECK_STATUS_OK(
      alert_handler_testutils_info_parse(dump, seg_size, &actual_info));

  if (round == kRound4) {
    // Check local alert only.
    // While testing ping timeout for local alert,
    // global alert ping timeout can be triggered
    // dut to short timeout value.
    // However, alert source of this ping timeout can be choosen randomly,
    // as documented in issue #2321, so we only check local alert cause.
    LOG_INFO("loc_alert_cause: exp: %08x   obs: %08x",
             kExpectedInfo[round].alert_info.loc_alert_cause,
             actual_info.loc_alert_cause);
    CHECK(kExpectedInfo[round].alert_info.loc_alert_cause ==
          actual_info.loc_alert_cause);
  } else {
    LOG_INFO("observed alert cause:");
    print_alert_cause(actual_info);
    LOG_INFO("expected alert cause:");
    print_alert_cause(kExpectedInfo[round].alert_info);
    for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
      CHECK(kExpectedInfo[round].alert_info.alert_cause[i] ==
                actual_info.alert_cause[i],
            "At alert cause %d Expected %d, got %d", i,
            kExpectedInfo[round].alert_info.alert_cause[i],
            actual_info.alert_cause[i]);
    }
  }

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    // We cannot do an "equal" check here since some of the alerts may
    // be fatal and cause the accumulated count to continuously grow.
    CHECK(kExpectedInfo[round].alert_info.class_accum_cnt[i] <=
              actual_info.class_accum_cnt[i],
          "alert_info.class_accum_cnt[%d] mismatch exp:0x%x  obs:0x%x", i,
          kExpectedInfo[round].alert_info.class_accum_cnt[i],
          actual_info.class_accum_cnt[i]);
  }
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    // added '<' because expected state can be minimum phase but
    // depends on simulation, sometimes it captures higher phase.
    CHECK(kExpectedInfo[round].alert_info.class_esc_state[i] <=
              actual_info.class_esc_state[i],
          "alert_info.class_esc_state[%d] mismatch exp:0x%x  obs:0x%x", i,
          kExpectedInfo[round].alert_info.class_esc_state[i],
          actual_info.class_esc_state[i]);
  }
}

static node_t test_node[kTopEarlgreyAlertPeripheralLast] = {
    [kTopEarlgreyAlertPeripheralSpiHost0] =
        {
            .name = "SPIHOST0",
            .alert = kTopEarlgreyAlertIdSpiHost0FatalFault,
            .class = kDifAlertHandlerClassB,
        },
    [kTopEarlgreyAlertPeripheralOtpCtrl] =
        {
            .name = "OTPCTRL",
            .alert = kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError,
            .class = kDifAlertHandlerClassB,
        },
    [kTopEarlgreyAlertPeripheralKmac] =
        {
            .name = "KMAC",
            .alert = kTopEarlgreyAlertIdKmacFatalFaultErr,
            .class = kDifAlertHandlerClassB,
        },
    [kTopEarlgreyAlertPeripheralUart0] =
        {
            .name = "UART0",
            .alert = kTopEarlgreyAlertIdUart0FatalFault,
            .class = kDifAlertHandlerClassC,
        },
    [kTopEarlgreyAlertPeripheralUart1] =
        {
            .name = "UART1",
            .alert = kTopEarlgreyAlertIdUart1FatalFault,
            .class = kDifAlertHandlerClassC,
        },
    [kTopEarlgreyAlertPeripheralUart2] =
        {
            .name = "UART2",
            .alert = kTopEarlgreyAlertIdUart2FatalFault,
            .class = kDifAlertHandlerClassC,
        },
    [kTopEarlgreyAlertPeripheralUart3] =
        {
            .name = "UART3",
            .alert = kTopEarlgreyAlertIdUart3FatalFault,
            .class = kDifAlertHandlerClassC,
        },
    [kTopEarlgreyAlertPeripheralI2c0] =
        {
            .name = "I2C0",
            .alert = kTopEarlgreyAlertIdI2c0FatalFault,
            .class = kDifAlertHandlerClassA,
        },
    [kTopEarlgreyAlertPeripheralI2c1] =
        {
            .name = "I2C1",
            .alert = kTopEarlgreyAlertIdI2c1FatalFault,
            .class = kDifAlertHandlerClassA,
        },
    [kTopEarlgreyAlertPeripheralI2c2] =
        {
            .name = "I2C2",
            .alert = kTopEarlgreyAlertIdI2c2FatalFault,
            .class = kDifAlertHandlerClassA,
        },
};

static void init_expected_cause() {
  kExpectedInfo[kRound1]
      .alert_info.alert_cause[kTopEarlgreyAlertIdI2c0FatalFault] = 1;
  kExpectedInfo[kRound1]
      .alert_info.alert_cause[kTopEarlgreyAlertIdI2c1FatalFault] = 1;
  kExpectedInfo[kRound1]
      .alert_info.alert_cause[kTopEarlgreyAlertIdI2c2FatalFault] = 1;

  kExpectedInfo[kRound2]
      .alert_info.alert_cause[kTopEarlgreyAlertIdUart0FatalFault] = 1;
  kExpectedInfo[kRound2]
      .alert_info.alert_cause[kTopEarlgreyAlertIdUart1FatalFault] = 1;
  kExpectedInfo[kRound2]
      .alert_info.alert_cause[kTopEarlgreyAlertIdUart2FatalFault] = 1;
  kExpectedInfo[kRound2]
      .alert_info.alert_cause[kTopEarlgreyAlertIdUart3FatalFault] = 1;
  kExpectedInfo[kRound2]
      .alert_info.alert_cause[kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError] = 1;

  kExpectedInfo[kRound3]
      .alert_info.alert_cause[kTopEarlgreyAlertIdRvCoreIbexRecovSwErr] = 1;
  kExpectedInfo[kRound3]
      .alert_info.alert_cause[kTopEarlgreyAlertIdUart0FatalFault] = 1;
  kExpectedInfo[kRound3]
      .alert_info.alert_cause[kTopEarlgreyAlertIdI2c0FatalFault] = 1;
  kExpectedInfo[kRound3]
      .alert_info.alert_cause[kTopEarlgreyAlertIdSpiHost0FatalFault] = 1;
};

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // set expected values
  init_expected_cause();

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  peripheral_init();

  // Enable all interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // First check the flash stored value.
  uint32_t event_idx = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &event_idx));

  // Enable flash access
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  // Increment flash counter to know where we are.
  CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(&flash_ctrl, 0));

  LOG_INFO("Test round %d", event_idx);

  // enable alert info
  CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr, kDifToggleEnabled));

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  LOG_INFO("reset info = 0x%02X", rst_info);
  global_alert_called = 0;

  // TODO(#13098): Change to equality after #13277 is merged.
  if (rst_info & kDifRstmgrResetInfoPor) {
    // We need to initialize the info FLASH partitions storing the Creator and
    // Owner secrets to avoid getting the flash controller into a fatal error
    // state.
    if (kDeviceType == kDeviceFpgaCw310 && rst_info & kDifRstmgrResetInfoPor) {
      CHECK_STATUS_OK(keymgr_testutils_flash_init(&flash_ctrl, &kCreatorSecret,
                                                  &kOwnerSecret));
    }

    global_test_round = kRound1;
    prgm_alert_handler_round1();

    CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c1, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c2, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

    // Give an enough delay until sw rest happens.
    busy_spin_micros(kRoundOneDelay);
    CHECK(false, "Should have reset before this line");
  } else if (rst_info == kDifRstmgrResetInfoSw && event_idx == 1) {
    collect_alert_dump_and_compare(kRound1);
    global_test_round = kRound2;
    prgm_alert_handler_round2();

    // Setup the aon_timer the wdog bark and bite timeouts.
    uint64_t bark_cycles =
        udiv64_slow(kWdogBarkMicros * kClockFreqAonHz, 1000000, NULL);
    uint64_t bite_cycles =
        udiv64_slow(kWdogBiteMicros * kClockFreqAonHz, 1000000, NULL);
    CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles,
                                                        bite_cycles, false));

    CHECK_DIF_OK(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault));
    CHECK_DIF_OK(dif_uart_alert_force(&uart1, kDifUartAlertFatalFault));
    CHECK_DIF_OK(dif_uart_alert_force(&uart2, kDifUartAlertFatalFault));
    CHECK_DIF_OK(dif_uart_alert_force(&uart3, kDifUartAlertFatalFault));
    CHECK_DIF_OK(dif_otp_ctrl_alert_force(&otp_ctrl,
                                          kDifOtpCtrlAlertFatalBusIntegError));
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassc, kDifToggleEnabled));

    busy_spin_micros(kRoundTwoDelay);
    CHECK(false, "Should have reset before this line");
  } else if (rst_info == kDifRstmgrResetInfoWatchdog) {
    collect_alert_dump_and_compare(kRound2);

    global_test_round = kRound3;
    prgm_alert_handler_round3();
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

    busy_spin_micros(kRoundThreeDelay);
    CHECK(false, "Should have reset before this line");
  } else if (rst_info == kDifRstmgrResetInfoEscalation && event_idx == 3) {
    collect_alert_dump_and_compare(kRound3);
    global_test_round = kRound4;
    prgm_alert_handler_round4();
    // Previously, this test assumed that escalation would always happen
    // within a fixed amount of time.  However, that is not necessarily
    // the case for ping timeouts.  The ping mechanism randomly selects a
    // peripheral to check.  However, since the selection vector is larger
    // than the number of peripherals we have, it does not always select a valid
    // peripheral. When the alert handler does not select a valid peripheral,
    // it simply moves on to the test the next ping. However the max wait time
    // until the next ping is checked is in the mS range.
    // Therefore, the test should not make that assumption and just wait in
    // place.
    wait_for_interrupt();
  } else if (rst_info == kDifRstmgrResetInfoEscalation && event_idx == 4) {
    collect_alert_dump_and_compare(kRound4);

    return true;
  } else {
    LOG_FATAL("unexpected reset info %d", rst_info);
  }

  return false;
}
