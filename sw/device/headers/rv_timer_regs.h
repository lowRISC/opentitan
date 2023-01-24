// Generated register defines for rv_timer

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _RV_TIMER_REG_DEFS_
#define _RV_TIMER_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of harts
#define RV_TIMER_PARAM_N_HARTS 1

// Number of timers per Hart
#define RV_TIMER_PARAM_N_TIMERS 1

// Number of alerts
#define RV_TIMER_PARAM_NUM_ALERTS 1

// Register width
#define RV_TIMER_PARAM_REG_WIDTH 32

// Alert Test Register
#define RV_TIMER_ALERT_TEST_REG_OFFSET 0x0
#define RV_TIMER_ALERT_TEST_REG_RESVAL 0x0
#define RV_TIMER_ALERT_TEST_FATAL_FAULT_BIT 0

// Control register (common parameters)
#define RV_TIMER_CTRL_ACTIVE_FIELD_WIDTH 1
#define RV_TIMER_CTRL_MULTIREG_COUNT 1

// Control register
#define RV_TIMER_CTRL_REG_OFFSET 0x4
#define RV_TIMER_CTRL_REG_RESVAL 0x0
#define RV_TIMER_CTRL_ACTIVE_0_BIT 0

// Interrupt Enable (common parameters)
#define RV_TIMER_INTR_ENABLE0_IE_FIELD_WIDTH 1
#define RV_TIMER_INTR_ENABLE0_MULTIREG_COUNT 1

// Interrupt Enable
#define RV_TIMER_INTR_ENABLE0_REG_OFFSET 0x100
#define RV_TIMER_INTR_ENABLE0_REG_RESVAL 0x0
#define RV_TIMER_INTR_ENABLE0_IE_0_BIT 0

// Interrupt Status (common parameters)
#define RV_TIMER_INTR_STATE0_IS_FIELD_WIDTH 1
#define RV_TIMER_INTR_STATE0_MULTIREG_COUNT 1

// Interrupt Status
#define RV_TIMER_INTR_STATE0_REG_OFFSET 0x104
#define RV_TIMER_INTR_STATE0_REG_RESVAL 0x0
#define RV_TIMER_INTR_STATE0_IS_0_BIT 0

// Interrupt test register (common parameters)
#define RV_TIMER_INTR_TEST0_T_FIELD_WIDTH 1
#define RV_TIMER_INTR_TEST0_MULTIREG_COUNT 1

// Interrupt test register
#define RV_TIMER_INTR_TEST0_REG_OFFSET 0x108
#define RV_TIMER_INTR_TEST0_REG_RESVAL 0x0
#define RV_TIMER_INTR_TEST0_T_0_BIT 0

// Configuration for Hart 0
#define RV_TIMER_CFG0_REG_OFFSET 0x10c
#define RV_TIMER_CFG0_REG_RESVAL 0x10000
#define RV_TIMER_CFG0_PRESCALE_MASK 0xfff
#define RV_TIMER_CFG0_PRESCALE_OFFSET 0
#define RV_TIMER_CFG0_PRESCALE_FIELD \
  ((bitfield_field32_t) { .mask = RV_TIMER_CFG0_PRESCALE_MASK, .index = RV_TIMER_CFG0_PRESCALE_OFFSET })
#define RV_TIMER_CFG0_STEP_MASK 0xff
#define RV_TIMER_CFG0_STEP_OFFSET 16
#define RV_TIMER_CFG0_STEP_FIELD \
  ((bitfield_field32_t) { .mask = RV_TIMER_CFG0_STEP_MASK, .index = RV_TIMER_CFG0_STEP_OFFSET })

// Timer value Lower
#define RV_TIMER_TIMER_V_LOWER0_REG_OFFSET 0x110
#define RV_TIMER_TIMER_V_LOWER0_REG_RESVAL 0x0

// Timer value Upper
#define RV_TIMER_TIMER_V_UPPER0_REG_OFFSET 0x114
#define RV_TIMER_TIMER_V_UPPER0_REG_RESVAL 0x0

// Timer value Lower
#define RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET 0x118
#define RV_TIMER_COMPARE_LOWER0_0_REG_RESVAL 0xffffffff

// Timer value Upper
#define RV_TIMER_COMPARE_UPPER0_0_REG_OFFSET 0x11c
#define RV_TIMER_COMPARE_UPPER0_0_REG_RESVAL 0xffffffff

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _RV_TIMER_REG_DEFS_
// End generated register defines for rv_timer