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

/**
 * RSTMGR ALERT_INFO Test
 *
 * This test runs some alert / dump scenario and check integrity of
 * ALERT_INFO coming from alert_hander to rstmgr.
 *
 * From dif_rstmgr_reset_info_t, there are 8 different resets.
 * This test covers 3 of those (kDifRstmgrResetInfoSw,
 * kDifRstmgrResetInfoWatchdog, kDifRstmgrResetInfoEscalation).
 * kDifRstmgrResetInfoNdm will be added as a separate test after ndm request
 * test is available. Test goes for 3 rounds, and on each round it creates a
 * different reset scenario.
 *
 * Round 1: Single Class profile
 * - Trigger alert from i2c0..2 by calling alert_force.
 * - This will trigger kDifAlertHandlerIrqClassa from alert_handler.
 * - Also alert_info start to transfer from alert_handler to rstmgr.
 * - Upon detecting interrupt, 'ottf_external_isr' request reset to rstmgr
 * - After reset, alert_info will be available at rstmgr.
 * - Read alert_info from rstmgr and compare with expected value.
 *
 * Round 2: Multi Classes profile
 * - Trigger alert from uart0..3 and otp_ctrl.
 * - Setup the aon_timer wdog bark and bite timeouts.
 * - Let the timer expire to create watchdog bite.
 * - After reset, coalescalationed alert info from uarts and otp_ctrl
 *   will be available from rstmgr.
 * - Read alert_info from rstmgr and compare with expected value.
 *
 * Round 3: All Classes profile with alert escalation
 * - Trigger local alert by alert handler ping timeout
 * - Trigger other alerts for all classes.
 * - local alert will be escalationalated to phase2 then it will trigger
 *   reset.
 * - Read alert_info from rstmgr and compare with expected value.
 */

enum {
  kWdogBarkMicros = 200,
  kWdogBiteMicros = 200,
  kEscalationPhase0Micros = 300,
  kEscalationPhase1Micros = 200,
  kEscalationPhase2Micros = 100,
  kRoundOneDelayMicros = 100,
  kRoundTwoDelayMicros = 100,
  kRoundThreeDelayMicros = 3000,
};

static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;

static dif_rstmgr_t rstmgr;
static dif_alert_handler_t alert_handler;
static dif_uart_t uart0;
static dif_uart_t uart1;
static dif_uart_t uart2;
static dif_uart_t uart3;
static dif_otp_ctrl_t otp_ctrl;
static dif_spi_host_t spi_host;
static dif_rv_plic_t plic;
static dif_aon_timer_t aon_timer;
static dif_pwrmgr_t pwrmgr;
static dif_i2c_t i2c0;
static dif_i2c_t i2c1;
static dif_i2c_t i2c2;

typedef struct test_case {
  const char *name;
  dif_alert_handler_alert_t alert;
  dif_alert_handler_class_t class;
} test_case_t;

typedef enum cstate {
  kCstateIdle = 0,
  kCstateTimeout = 1,
  kCstateTerminal = 3,
  kCstatePhase0 = 4,
  kCstatePhase1 = 5,
  kCstatePhase2 = 6,
  kCstatePhase3 = 7,
  kCstateFsmError = 2,
} cstate_t;

typedef struct alert_info {
  const char *test_name;
  /**
   * 61 bits alert cause.
   */
  uint64_t alert_cause;
  /**
   * 7 bit local alert cause.
   */
  uint8_t loc_alert_cause;
  /**
   * Accumulator coutns for each alert class.
   */
  uint16_t class_accumulated_count[ALERT_HANDLER_PARAM_N_CLASSES];
  /**
   * Escalation counts for each alert class.
   */
  uint32_t class_escalation_count[ALERT_HANDLER_PARAM_N_CLASSES];
  /**
   * Escalation states for each alert class.
   */
  cstate_t class_escalation_state[ALERT_HANDLER_PARAM_N_CLASSES];
} alert_info_t;

static uint64_t merge32(uint32_t x, uint32_t y) {
  uint64_t pow = 10;
  while (y >= pow) {
    pow *= 10;
  }
  return x * pow + y;
}

/**
 * Copies `bit_count` bits starting at `bit_offset`. This function internally
 * perfroms shifts to fix things up.
 */
static void read_bits(void *dest, const void *src, size_t bit_offset,
                      size_t bit_count) {
  char *dest8 = dest;
  const char *src8 = src;
  src8 += bit_offset / 8;

  size_t shift = bit_offset % 8;
  size_t antishift = 8 - shift;
  while (bit_count > 0) {
    char mask = bit_count < 8 ? (1u << bit_count) - 1 : -1;
    *dest8 = (src8[0] >> shift) & mask;

    if (bit_count < antishift) {
      break;
    }
    bit_count -= antishift;
    if (bit_count > 0 && shift > 0) {
      char mask = bit_count < 8 ? (1u << bit_count) - 1 : -1;
      *dest8 |= (src8[1] & mask) << (8 - shift);
      if (bit_count < shift) {
        break;
      }
      bit_count -= shift;
    }
    ++dest8;
    ++src8;
  }
}

static alert_info_t alert_info_from_dump(
    dif_rstmgr_alert_info_dump_segment_t *dump) {
  alert_info_t info = {0};

  // The dump has the following layout, as a packed struct:
  // struct {
  //   u3[N] escalation_states;
  //   u32[N] escalation_counts;
  //   u16[N] accumulated_count;
  //   u7 local_alert_cause;
  //   u63 alert_cause;
  // }

  size_t bit_cursor = 0;
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    read_bits(&info.class_escalation_state[i], dump, bit_cursor, 3);
    bit_cursor += 3;
  }

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    read_bits(&info.class_escalation_count[i], dump, bit_cursor, 32);
    bit_cursor += 32;
  }

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    read_bits(&info.class_accumulated_count[i], dump, bit_cursor, 16);
    bit_cursor += 16;
  }

  read_bits(&info.loc_alert_cause, dump, bit_cursor, 7);
  bit_cursor += 7;

  uint32_t lo, hi;
  read_bits(&lo, dump, bit_cursor, 32);
  read_bits(&hi, dump, bit_cursor + 32, 32);
  info.alert_cause = merge32(hi, lo);

  return info;
}

static const dif_alert_handler_escalation_phase_t
    kEscalationProfiles[][ALERT_HANDLER_PARAM_N_CLASSES] = {
        [kDifAlertHandlerClassA] =
            {
                {
                    .phase = kDifAlertHandlerClassStatePhase0,
                    .signal = 0,
                    .duration_cycles = 5000,
                },
                {
                    .phase = kDifAlertHandlerClassStatePhase1,
                    .signal = 0,
                    .duration_cycles = 3000,
                },
            },
        [kDifAlertHandlerClassB] = {{
            .phase = kDifAlertHandlerClassStatePhase1,
            .signal = 0,
            .duration_cycles = 3000,
        }},
        [kDifAlertHandlerClassC] =
            {
                {
                    .phase = kDifAlertHandlerClassStatePhase0,
                    .signal = 0,
                    .duration_cycles = 5000,
                },
                {
                    .phase = kDifAlertHandlerClassStatePhase1,
                    .signal = 0,
                    .duration_cycles = 3000,
                },
            },
        [kDifAlertHandlerClassD] =
            {
                {
                    .phase = kDifAlertHandlerClassStatePhase0,
                    .signal = 0,
                    .duration_cycles = 7200,
                },
                {
                    .phase = kDifAlertHandlerClassStatePhase1,
                    .signal = 1,
                    .duration_cycles = 4800,
                },
                {
                    .phase = kDifAlertHandlerClassStatePhase2,
                    .signal = 3,
                    .duration_cycles = 2400,
                },
            },
};

static const dif_alert_handler_class_config_t
    kConfigProfiles[ALERT_HANDLER_PARAM_N_CLASSES] = {
        [kDifAlertHandlerClassA] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases =
                    kEscalationProfiles[kDifAlertHandlerClassA],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassB] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases =
                    kEscalationProfiles[kDifAlertHandlerClassB],
                .escalation_phases_len = 1,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassC] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 240,
                .escalation_phases =
                    kEscalationProfiles[kDifAlertHandlerClassC],
                .escalation_phases_len = 2,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase1,
            },
        [kDifAlertHandlerClassD] =
            {
                .auto_lock_accumulation_counter = kDifToggleDisabled,
                .accumulator_threshold = 0,
                .irq_deadline_cycles = 1000,
                .escalation_phases =
                    kEscalationProfiles[kDifAlertHandlerClassD],
                .escalation_phases_len = 3,
                .crashdump_escalation_phase = kDifAlertHandlerClassStatePhase3,
            },
};

static const alert_info_t kExpectedInfo[] = {
    {
        .test_name = "Single class (Class A)",
        .alert_cause = 0x1c0,
        .class_accumulated_count = {3, 0, 0, 0},
        .class_escalation_state = {kCstatePhase0, kCstateIdle, kCstateIdle,
                                   kCstateIdle},
    },
    {
        .test_name = "Multi classes (Class B, C)",
        .alert_cause = 0x400f,
        .class_accumulated_count = {0, 1, 4, 0},
        .class_escalation_state = {kCstateIdle, kCstatePhase1, kCstatePhase0,
                                   kCstateIdle},
    },
    {
        .test_name = "All classes",
        .alert_cause = 0x40041,
        .class_accumulated_count = {1, 1, 1, 2},
        .class_escalation_state = {kCstatePhase0, kCstatePhase1, kCstatePhase0,
                                   kCstatePhase0},
    },
};

static volatile bool global_alert_called;
static void set_extra_alert(void) {
  CHECK_DIF_OK(dif_uart_alert_force(&uart0, kDifUartAlertFatalFault));
  CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
  CHECK_DIF_OK(dif_spi_host_alert_force(&spi_host, kDifSpiHostAlertFatalFault));
  global_alert_called = true;
}

static volatile int global_test_round;

/**
 * External ISR.
 *
 * Handles all peripheral interrupts on Ibex. PLIC asserts an external interrupt
 * line to the CPU, which results in a call to this OTTF ISR. This ISR
 * overrides the default OTTF implementation.
 */
void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &irq_id));

  top_earlgrey_plic_peripheral_t peripheral =
      top_earlgrey_plic_interrupt_for_peripheral[irq_id];

  LOG_INFO("IRQ: round: %d; got irq %d from peripheral: %d", global_test_round,
           irq_id, peripheral);

  if (peripheral == kTopEarlgreyPlicPeripheralAonTimerAon) {
    uint32_t irq = irq_id - kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired;
    CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer, irq));
  } else if (peripheral == kTopEarlgreyPlicPeripheralAlertHandler) {
    uint32_t irq = irq_id - kTopEarlgreyPlicIrqIdAlertHandlerClassa;

    LOG_INFO("IRQ: %d", irq);
    switch (irq) {
      case 0:  // Class A.
        CHECK_DIF_OK(dif_alert_handler_alert_acknowledge(
            &alert_handler, kDifI2cAlertFatalFault));

        dif_alert_handler_class_state_t state;
        CHECK_DIF_OK(dif_alert_handler_get_class_state(
            &alert_handler, kDifAlertHandlerClassA, &state));
        LOG_INFO("IRQ: state = %d", state);

        if (global_test_round == 1) {
          LOG_INFO("IRQ: kick off SW reset!");
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
        if (!global_alert_called) {
          LOG_INFO("IRQ: extra alert called");
          set_extra_alert();
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
static void prgm_alert_handler_round1(const test_case_t *tests) {
  dif_alert_handler_class_t alert_class = kDifAlertHandlerClassA;

  for (int i = kTopEarlgreyAlertPeripheralI2c0;
       i < kTopEarlgreyAlertPeripheralI2c2 + 1; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, tests[i].alert, tests[i].class,
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
 *
 * Configure alert from aon timer
 * .alert class = class B
 * .escalation phases 1
 *
 * Set escalation_phases.signal = 0 for all cases to avoid
 * watchdog timer freeze.
 */
static void prgm_alert_handler_round2(const test_case_t *tests) {
  dif_alert_handler_class_t alert_classes[] = {
      kDifAlertHandlerClassC,
      kDifAlertHandlerClassB,
  };
  dif_alert_handler_class_config_t class_configs[] = {
      kConfigProfiles[kDifAlertHandlerClassC],
      kConfigProfiles[kDifAlertHandlerClassB],
  };

  for (size_t i = kTopEarlgreyAlertPeripheralUart0;
       i < kTopEarlgreyAlertPeripheralUart3 + 1; ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, tests[i].alert, tests[i].class,
        /*enabled=*/kDifToggleEnabled, /*locked=*/kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_alert_handler_configure_alert(
      &alert_handler, tests[kTopEarlgreyAlertPeripheralOtpCtrl].alert,
      tests[kTopEarlgreyAlertPeripheralOtpCtrl].class,
      /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  for (size_t i = 0; i < ARRAYSIZE(alert_classes); ++i) {
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

static void prgm_alert_handler_round3() {
  // Enable all incoming alerts. This will create ping timeout event
  // for all possible alert and will see the timeout more often.

  for (size_t i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    dif_alert_handler_class_t alert_class;
    switch (i) {
      case kTopEarlgreyAlertIdSpiHost0FatalFault:
      case kTopEarlgreyAlertIdOtpCtrlFatalCheckError:
      case kTopEarlgreyAlertIdKmacFatalFaultErr:
        alert_class = kDifAlertHandlerClassB;
        break;
      case kTopEarlgreyAlertIdUart0FatalFault:
        alert_class = kDifAlertHandlerClassC;
        break;
      case kTopEarlgreyAlertIdI2c0FatalFault:
        alert_class = kDifAlertHandlerClassA;
        break;
      default:
        alert_class = kDifAlertHandlerClassD;
        break;
    }

    CHECK_DIF_OK(dif_alert_handler_configure_alert(
        &alert_handler, i, alert_class, /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }

  dif_alert_handler_class_t alert_classes[] = {
      kDifAlertHandlerClassA,
      kDifAlertHandlerClassB,
      kDifAlertHandlerClassC,
      kDifAlertHandlerClassD,
  };

  dif_alert_handler_class_config_t class_configs[] = {
      kConfigProfiles[kDifAlertHandlerClassA],
      kConfigProfiles[kDifAlertHandlerClassB],
      kConfigProfiles[kDifAlertHandlerClassC],
      kConfigProfiles[kDifAlertHandlerClassD],
  };

  CHECK_DIF_OK(dif_alert_handler_configure_local_alert(
      &alert_handler, kDifAlertHandlerLocalAlertAlertPingFail,
      kDifAlertHandlerClassD, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));

  for (size_t i = 0; i < ARRAYSIZE(alert_classes); ++i) {
    CHECK_DIF_OK(dif_alert_handler_configure_class(
        &alert_handler, alert_classes[i], class_configs[i],
        /*enabled=*/kDifToggleEnabled,
        /*locked=*/kDifToggleEnabled));
  }

  CHECK_DIF_OK(dif_alert_handler_configure_ping_timer(
      &alert_handler, 2, /*enabled=*/kDifToggleEnabled,
      /*locked=*/kDifToggleEnabled));
}

static void init_peripherals(void) {
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_alert_handler_init(
      mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR),
      &alert_handler));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

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

  // Set pwrmgr reset enable.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
}

static dif_rstmgr_alert_info_dump_segment_t
    dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];

static void collect_alert_dump_and_compare(int round_number) {
  size_t seg_size;
  CHECK_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &seg_size));

  LOG_INFO("test name: %s, dump size: %d",
           kExpectedInfo[round_number].test_name, seg_size);
  for (int i = 0; i < seg_size; ++i) {
    LOG_INFO("dump[%d] 0x%08x", i, dump[i]);
  }

  alert_info_t actual_info = alert_info_from_dump(dump);
  LOG_INFO("alert_cause: 0x%x", actual_info.alert_cause);

  CHECK(kExpectedInfo[round_number].alert_cause == actual_info.alert_cause,
        "alert_info.alert_cause mismatch: want: 0x%x got: 0x%x",
        kExpectedInfo[round_number].alert_cause, actual_info.alert_cause);

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    uint32_t want = kExpectedInfo[round_number].class_accumulated_count[i];
    uint32_t got = actual_info.class_accumulated_count[i];
    CHECK(
        want == got,
        "alert_info.class_accumulated_count[%d] mismatch: want: 0x%x got: 0x%x",
        i, want, got);
  }

  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    uint32_t want = kExpectedInfo[round_number].class_escalation_state[i];
    uint32_t got = actual_info.class_escalation_state[i];
    // added '<' because expected state can be minimum phase but
    // depends on simulation, sometimes it captures higher phase.
    CHECK(
        want <= got,
        "alert_info.class_escalation_state[%d] mismatch: want: 0x%x got: 0x%x",
        i, want, got);
  }
}

static const test_case_t kTests[kTopEarlgreyAlertPeripheralLast] = {
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

bool test_main(void) {
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  init_peripherals();

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
  global_alert_called = false;
  switch (rst_info) {
    case kDifRstmgrResetInfoPor: {
      global_test_round = 1;
      prgm_alert_handler_round1(kTests);

      LOG_INFO("ALERT1");
      CHECK_DIF_OK(dif_i2c_alert_force(&i2c0, kDifI2cAlertFatalFault));
      CHECK_DIF_OK(dif_i2c_alert_force(&i2c1, kDifI2cAlertFatalFault));
      CHECK_DIF_OK(dif_i2c_alert_force(&i2c2, kDifI2cAlertFatalFault));
      CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
          &alert_handler, kDifAlertHandlerIrqClassa, kDifToggleEnabled));

      // Give an enough delay until sw rest happens.
      LOG_INFO("wait for round 1: 100us");
      busy_spin_micros(kRoundOneDelayMicros);
      return true;
    }
    case kDifRstmgrResetInfoSw: {
      collect_alert_dump_and_compare(1);
      global_test_round = 2;

      prgm_alert_handler_round2(kTests);

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
      CHECK_DIF_OK(dif_otp_ctrl_alert_force(
          &otp_ctrl, kDifOtpCtrlAlertFatalBusIntegError));
      CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
          &alert_handler, kDifAlertHandlerIrqClassb, kDifToggleEnabled));
      CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
          &alert_handler, kDifAlertHandlerIrqClassc, kDifToggleEnabled));

      LOG_INFO("wait for round 2; 100us");
      busy_spin_micros(kRoundTwoDelayMicros);
      return true;
    }
    case kDifRstmgrResetInfoWatchdog: {
      collect_alert_dump_and_compare(2);

      global_test_round = 3;
      prgm_alert_handler_round3();
      CHECK_DIF_OK(dif_alert_handler_irq_set_enabled(
          &alert_handler, kDifAlertHandlerIrqClassd, kDifToggleEnabled));

      LOG_INFO("wait for round 3; 3ms");
      busy_spin_micros(kRoundThreeDelayMicros);
      return true;
    }
    case kDifRstmgrResetInfoEscalation: {
      collect_alert_dump_and_compare(3);
      return true;
    }
    default: {
      LOG_FATAL("unexpected reset info %d", rst_info);
      return false;
    }
  }
}
