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
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/alert_handler_testutils.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
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
  - Trigger local alert by alert handler ping timeout
  - Trigger other alerts for all classes.
  - local alert will be escalated to phase2 then it will trigger
    reset.
  - Read alert_info from rstmgr and compare with expected value.


 */

enum {
  kWdogBarkMicros = 200,          // us
  kWdogBiteMicros = 200,          // us
  kEscalationPhase0Micros = 300,  // us
  kEscalationPhase1Micros = 200,  // us
  kEscalationPhase2Micros = 100,  // us
  kRoundOneDelay = 100,           // us
  kRoundTwoDelay = 100,           // us
  kRoundThreeDelay = 3000,        // us
};

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_uart_t uart0, uart1, uart2, uart3;
static dif_otp_ctrl_t otp_ctrl;
static dif_spi_host_t spi_host;
static dif_rv_plic_t plic;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_i2c_t i2c0, i2c1, i2c2;

static uint64_t merge32(uint32_t x, uint32_t y) {
  uint64_t pow = 10;
  while (y >= pow) {
    pow *= 10;
  }
  return (uint64_t)(x * pow + y);
}

typedef struct node {
  const char *name;
  dif_alert_handler_alert_t alert;
  dif_alert_handler_class_t class;
} node_t;

typedef enum cstate {
  kCstateIdle = 0,
  kCstateTimeout = 1,
  kCstateTerminal = 3,
  kCstatePhase0 = 4,
  kCstatePhase1 = 5,
  kCstatePhase2 = 6,
  kCstatePhase3 = 7,
  kCstateFsmError = 2
} cstate_t;

typedef enum test_round {
  kRound1 = 0,
  kRound2 = 1,
  kRound3 = 2,
  kRoundTotal = 3
} test_round_t;

typedef struct alert_info {
  char *test_name;
  uint64_t alert_cause;                                     // 61bit
  uint8_t loc_alert_cause;                                  // 7bit
  uint16_t class_accum_cnt[ALERT_HANDLER_PARAM_N_CLASSES];  // 4x16bit
  uint32_t class_esc_cnt[ALERT_HANDLER_PARAM_N_CLASSES];    // 4x32bit
  cstate_t class_esc_state[ALERT_HANDLER_PARAM_N_CLASSES];  // 4x3bit
} alert_info_t;

static test_round_t global_test_round;
static uint32_t global_alert_called;
static dif_alert_handler_escalation_phase_t
    esc_profiles[][ALERT_HANDLER_PARAM_N_CLASSES] = {
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
static dif_alert_handler_class_config_t
    config_profiles[ALERT_HANDLER_PARAM_N_CLASSES] = {
        [kDifAlertHandlerClassA] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = esc_profiles[kDifAlertHandlerClassA],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassB] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = esc_profiles[kDifAlertHandlerClassB],
                .escalation_phases_len = 1,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassC] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases = esc_profiles[kDifAlertHandlerClassC],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassD] = {
            .auto_lock_accumulation_counter = kDifToggleDisabled,
            .accumulator_threshold = 0,
            .irq_deadline_cycles = 1000,
            .escalation_phases = esc_profiles[kDifAlertHandlerClassD],
            .escalation_phases_len = 3,
            .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
        }};

static alert_info_t expected_info[kRoundTotal] = {
    [kRound1] =
        {
            .test_name = "Single class(ClassA)",
            .alert_cause = 0x1c0,
            .class_accum_cnt = {3, 0, 0, 0},
            .class_esc_state = {kCstatePhase0, kCstateIdle, kCstateIdle,
                                kCstateIdle},
        },
    [kRound2] =
        {
            .test_name = "Multi classes(ClassB,C)",
            .alert_cause = 0x400f,
            .class_accum_cnt = {0, 1, 4, 0},
            .class_esc_state = {kCstateIdle, kCstatePhase1, kCstatePhase0,
                                kCstateIdle},
        },
    [kRound3] = {
        .test_name = "All classes",
        .alert_cause = 0x40041,
        .class_accum_cnt = {1, 1, 1, 2},
        .class_esc_state = {kCstatePhase0, kCstatePhase1, kCstatePhase0,
                            kCstatePhase0},
    }};

static alert_info_t alert_info_dump2struct(
    dif_rstmgr_alert_info_dump_segment_t *dump) {
  alert_info_t myinfo = {
      .class_esc_state = {(cstate_t)(dump[0] & 0x7),
                          (cstate_t)((dump[0] >> 3) & 0x7),
                          (cstate_t)((dump[0] >> 6) & 0x7),
                          (cstate_t)((dump[0] >> 9) & 0x7)},
  };
  // class_esc_cnt
  uint32_t upper, lower;

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    lower = dump[i] >> 12;
    upper = dump[i + 1] << 20;
    myinfo.class_esc_cnt[i] = upper | lower;
  }
  // class_accum_cnt
  myinfo.class_accum_cnt[0] = (uint16_t)(dump[4] >> 12);
  lower = dump[4] >> 28;
  upper = dump[5] << 8;
  myinfo.class_accum_cnt[1] = (uint16_t)(upper | lower);
  myinfo.class_accum_cnt[2] = (uint16_t)(dump[5] >> 12);
  lower = dump[5] >> 28;
  upper = dump[6] << 8;
  myinfo.class_accum_cnt[3] = (uint16_t)(upper | lower);
  // loc_alert_cause
  myinfo.loc_alert_cause = (dump[6] >> 12) & 0x7f;
  // alert_cause
  lower = dump[7] & 0xffff;
  upper = dump[7] >> 16;

  // dump[6] layout:
  //  31                     19,
  // |--- alert_cause[12:0]---+
  // 18                    12,11 0
  // +--loc_alert_cause[6:0]--+--class_accum_cnt[3][15:4]--|
  //
  // total 16 + 13 lower bits are valid
  lower = (lower << 13) + (dump[6] >> 19);

  // dump[8] lower16 + dump[7] upper 16
  upper = upper + ((dump[8] & 0xffff) << 16);
  myinfo.alert_cause = merge32(upper, lower);

  return myinfo;
}

static node_t test_node[kTopEarlgreyAlertPeripheralLast];

static void set_extra_alert(uint32_t *set) {
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

  LOG_INFO("round:%d  I GOT IRQ %d from peripheral:%d", global_test_round,
           irq_id, peripheral);

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    irq = (dif_aon_timer_irq_t)(
        irq_id -
        (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);

    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    irq = (irq_id -
           (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);

    LOG_INFO("IRQ2: %d", irq);

    switch (irq) {
      case 0:  // class a
        CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
            &alert_handler, kDifI2cAlertFatalFault));

        // check classes
        dif_alert_handler_class_state_t state;
        CHECK_DIF_OK(dif_alert_handler_get_class_state(
            &alert_handler, kDifAlertHandlerClassA, &state));
        LOG_INFO("IRQ: state :  %d", state);

        // sw reset for round 1
        if (global_test_round == kRound1) {
          LOG_INFO("IRQ: kick off sw reset!!");
          CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
        }
        CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));

        break;
      case 1:
        LOG_INFO("IRQ: class B");
        break;
      case 2:
        LOG_INFO("IRQ: class C");
        break;
      case 3:
        LOG_INFO("IRQ: class D");
        if (global_alert_called == 0) {
          LOG_INFO("IRQ: extra alert called");
          set_extra_alert(&global_alert_called);
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
      &alert_handler, alert_class, config_profiles[alert_class],
      /*enabled=*/kDifToggleEnabled, /*locked=*/kDifToggleEnabled));
  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 0, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));
}

/*
 * Configure alert for uart0..3
 * .alert class = class C
 * .escalation phase0,1
 *
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
      config_profiles[kDifAlertHandlerClassC],
      config_profiles[kDifAlertHandlerClassB]};

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
 *     the rest to class d (including local alert)
 *
 * For class d, enable 3 phases and escalation reset will be
 * triggered at phase2
 */

static void prgm_alert_handler_round3(void) {
  // Enable all incoming alerts. This will create ping timeout event
  // for all possible alert and will see the timeout more often
  dif_alert_handler_class_t alert_class;

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    if (i == kTopEarlgreyAlertIdSpiHost0FatalFault ||
        i == kTopEarlgreyAlertIdOtpCtrlFatalCheckError ||
        i == kTopEarlgreyAlertIdKmacFatalFaultErr) {
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

  dif_alert_handler_class_config_t class_configs[] = {
      config_profiles[kDifAlertHandlerClassA],
      config_profiles[kDifAlertHandlerClassB],
      config_profiles[kDifAlertHandlerClassC],
      config_profiles[kDifAlertHandlerClassD]};

  CHECK_DIF_OK(dif_alert_handler_configure_local_alert(
      &alert_handler, kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerClassD, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  for (int i = 0; i < ARRAYSIZE(alert_classes); ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_classes[i], class_configs[i],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 2, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));
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

  // Set pwrmgr reset_en
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
}

static dif_rstmgr_alert_info_dump_segment_t
    dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
static void collect_alert_dump_and_compare(test_round_t round) {
  size_t seg_size;
  alert_info_t actual_info;

  CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &seg_size));

  LOG_INFO("Testname: %s  DUMP SIZE %d", expected_info[round].test_name,
           seg_size);
  for (int i = 0; i < seg_size; i++) {
    LOG_INFO("DUMP:%d: 0x%x", i, dump[i]);
  }

  actual_info = alert_info_dump2struct(dump);

  LOG_INFO("alert_cause : 0x%x", actual_info.alert_cause);

  CHECK(expected_info[round].alert_cause == actual_info.alert_cause,
        "alert_info.alert_cause mismatch exp:0x%x  obs:0x%x",
        expected_info[round].alert_cause, actual_info.alert_cause);
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    CHECK(expected_info[round].class_accum_cnt[i] ==
              actual_info.class_accum_cnt[i],
          "alert_info.class_accum_cnt[%d] mismatch exp:0x%x  obs:0x%x", i,
          expected_info[round].class_accum_cnt[i],
          actual_info.class_accum_cnt[i]);
  }
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    // added '<' because expected state can be minimum phase but
    // depends on simulation, sometimes it captures higher phase.
    CHECK(expected_info[round].class_esc_state[i] <=
              actual_info.class_esc_state[i],
          "alert_info.class_esc_state[%d] mismatch exp:0x%x  obs:0x%x", i,
          expected_info[round].class_esc_state[i],
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
    [kTopEarlgreyAlertPeripheralI2c2] = {
        .name = "I2C2",
        .alert = kTopEarlgreyAlertIdI2c2FatalFault,
        .class = kDifAlertHandlerClassA,
    }};

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  peripheral_init();

  // Enable all interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassa,
                                     kTopEarlgreyPlicIrqIdAlertHandlerClassd);
  rv_plic_testutils_irq_range_enable(
      &plic, kPlicTarget, kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired,
      kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark);

  // enable alert info
  CHECK_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr, kDifToggleEnabled));

  // Check if there was a HW reset caused by the escalation.
  dif_rstmgr_reset_info_bitfield_t rst_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &rst_info));
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  LOG_INFO("reset info = 0x%02X", rst_info);
  global_alert_called = 0;

  if (rst_info == kDifRstmgrResetInfoPor) {
    global_test_round = kRound1;
    prgm_alert_handler_round1();

    LOG_INFO("ALERT1");
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c1, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_i2c_alert_force(&i2c2, kDifI2cAlertFatalFault));
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

    // Give an enough delay until sw rest happens.
    LOG_INFO("wait round1 100us");
    busy_spin_micros(kRoundOneDelay);

  } else if (rst_info == kDifRstmgrResetInfoSw) {
    collect_alert_dump_and_compare(kRound1);
    global_test_round = kRound2;

    prgm_alert_handler_round2();

    LOG_INFO("ALERT2");
    // Setup the aon_timer the wdog bark and bite timeouts.
    uint64_t bark_cycles =
        udiv64_slow(kWdogBarkMicros * kClockFreqAonHz, 1000000, NULL);
    uint64_t bite_cycles =
        udiv64_slow(kWdogBiteMicros * kClockFreqAonHz, 1000000, NULL);
    aon_timer_testutils_watchdog_config(&aon_timer, bark_cycles, bite_cycles,
                                        false);

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

    LOG_INFO("wait round2 100us");
    busy_spin_micros(kRoundTwoDelay);
  } else if (rst_info == kDifRstmgrResetInfoWatchdog) {
    collect_alert_dump_and_compare(kRound2);

    global_test_round = kRound3;
    prgm_alert_handler_round3();
    CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
        &alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

    LOG_INFO("wait round3 3ms");
    busy_spin_micros(kRoundThreeDelay);
  } else if (rst_info == kDifRstmgrResetInfoEscalation) {
    collect_alert_dump_and_compare(kRound3);
  } else {
    LOG_FATAL("unexpected reset info %d", rst_info);
  }

  return true;
}
