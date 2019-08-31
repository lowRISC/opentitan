// Generated register defines for rv_timer

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _RV_TIMER_REG_DEFS_
#define _RV_TIMER_REG_DEFS_

// Control register
#define RV_TIMER_CTRL(id) (RV_TIMER##id##_BASE_ADDR + 0x0)
#define RV_TIMER_CTRL_ACTIVE0 0

// Configuration for Hart 0
#define RV_TIMER_CFG0(id) (RV_TIMER##id##_BASE_ADDR + 0x100)
#define RV_TIMER_CFG0_PRESCALE_MASK 0xfff
#define RV_TIMER_CFG0_PRESCALE_OFFSET 0
#define RV_TIMER_CFG0_STEP_MASK 0xff
#define RV_TIMER_CFG0_STEP_OFFSET 16

// Timer value Lower
#define RV_TIMER_TIMER_V_LOWER0(id) (RV_TIMER##id##_BASE_ADDR + 0x104)

// Timer value Upper
#define RV_TIMER_TIMER_V_UPPER0(id) (RV_TIMER##id##_BASE_ADDR + 0x108)

// Timer value Lower
#define RV_TIMER_COMPARE_LOWER0_0(id) (RV_TIMER##id##_BASE_ADDR + 0x10c)

// Timer value Upper
#define RV_TIMER_COMPARE_UPPER0_0(id) (RV_TIMER##id##_BASE_ADDR + 0x110)

// Interrupt Enable
#define RV_TIMER_INTR_ENABLE0(id) (RV_TIMER##id##_BASE_ADDR + 0x114)
#define RV_TIMER_INTR_ENABLE0_IE0 0

// Interrupt Status
#define RV_TIMER_INTR_STATE0(id) (RV_TIMER##id##_BASE_ADDR + 0x118)
#define RV_TIMER_INTR_STATE0_IS0 0

// Interrupt test register
#define RV_TIMER_INTR_TEST0(id) (RV_TIMER##id##_BASE_ADDR + 0x11c)
#define RV_TIMER_INTR_TEST0_T0 0

#endif  // _RV_TIMER_REG_DEFS_
// End generated register defines for rv_timer
