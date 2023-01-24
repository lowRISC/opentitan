// Generated register defines for aon_timer

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _AON_TIMER_REG_DEFS_
#define _AON_TIMER_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of alerts
#define AON_TIMER_PARAM_NUM_ALERTS 1

// Register width
#define AON_TIMER_PARAM_REG_WIDTH 32

// Alert Test Register
#define AON_TIMER_ALERT_TEST_REG_OFFSET 0x0
#define AON_TIMER_ALERT_TEST_REG_RESVAL 0x0
#define AON_TIMER_ALERT_TEST_FATAL_FAULT_BIT 0

// Wakeup Timer Control register
#define AON_TIMER_WKUP_CTRL_REG_OFFSET 0x4
#define AON_TIMER_WKUP_CTRL_REG_RESVAL 0x0
#define AON_TIMER_WKUP_CTRL_ENABLE_BIT 0
#define AON_TIMER_WKUP_CTRL_PRESCALER_MASK 0xfff
#define AON_TIMER_WKUP_CTRL_PRESCALER_OFFSET 1
#define AON_TIMER_WKUP_CTRL_PRESCALER_FIELD \
  ((bitfield_field32_t) { .mask = AON_TIMER_WKUP_CTRL_PRESCALER_MASK, .index = AON_TIMER_WKUP_CTRL_PRESCALER_OFFSET })

// Wakeup Timer Threshold Register
#define AON_TIMER_WKUP_THOLD_REG_OFFSET 0x8
#define AON_TIMER_WKUP_THOLD_REG_RESVAL 0x0

// Wakeup Timer Count Register
#define AON_TIMER_WKUP_COUNT_REG_OFFSET 0xc
#define AON_TIMER_WKUP_COUNT_REG_RESVAL 0x0

// Watchdog Timer Write Enable Register
#define AON_TIMER_WDOG_REGWEN_REG_OFFSET 0x10
#define AON_TIMER_WDOG_REGWEN_REG_RESVAL 0x1
#define AON_TIMER_WDOG_REGWEN_REGWEN_BIT 0

// Watchdog Timer Control register
#define AON_TIMER_WDOG_CTRL_REG_OFFSET 0x14
#define AON_TIMER_WDOG_CTRL_REG_RESVAL 0x0
#define AON_TIMER_WDOG_CTRL_ENABLE_BIT 0
#define AON_TIMER_WDOG_CTRL_PAUSE_IN_SLEEP_BIT 1

// Watchdog Timer Bark Threshold Register
#define AON_TIMER_WDOG_BARK_THOLD_REG_OFFSET 0x18
#define AON_TIMER_WDOG_BARK_THOLD_REG_RESVAL 0x0

// Watchdog Timer Bite Threshold Register
#define AON_TIMER_WDOG_BITE_THOLD_REG_OFFSET 0x1c
#define AON_TIMER_WDOG_BITE_THOLD_REG_RESVAL 0x0

// Watchdog Timer Count Register
#define AON_TIMER_WDOG_COUNT_REG_OFFSET 0x20
#define AON_TIMER_WDOG_COUNT_REG_RESVAL 0x0

// Interrupt State Register
#define AON_TIMER_INTR_STATE_REG_OFFSET 0x24
#define AON_TIMER_INTR_STATE_REG_RESVAL 0x0
#define AON_TIMER_INTR_STATE_WKUP_TIMER_EXPIRED_BIT 0
#define AON_TIMER_INTR_STATE_WDOG_TIMER_BARK_BIT 1

// Interrupt Test Register
#define AON_TIMER_INTR_TEST_REG_OFFSET 0x28
#define AON_TIMER_INTR_TEST_REG_RESVAL 0x0
#define AON_TIMER_INTR_TEST_WKUP_TIMER_EXPIRED_BIT 0
#define AON_TIMER_INTR_TEST_WDOG_TIMER_BARK_BIT 1

// Wakeup request status
#define AON_TIMER_WKUP_CAUSE_REG_OFFSET 0x2c
#define AON_TIMER_WKUP_CAUSE_REG_RESVAL 0x0
#define AON_TIMER_WKUP_CAUSE_CAUSE_BIT 0

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _AON_TIMER_REG_DEFS_
// End generated register defines for aon_timer