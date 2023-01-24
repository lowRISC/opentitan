// Generated register defines for PWRMGR

// Copyright information found in source file:
// Copyright lowRISC contributors.Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _PWRMGR_REG_DEFS_
#define _PWRMGR_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of wakeups
#define PWRMGR_PARAM_NUM_WKUPS 4

// Vector index for sysrst_ctrl_aon wkup_req, applies for WAKEUP_EN,
// WAKE_STATUS and WAKE_INFO
#define PWRMGR_PARAM_SYSRST_CTRL_AON_WKUP_REQ_IDX 0

// Vector index for pinmux_aon pin_wkup_req, applies for WAKEUP_EN,
// WAKE_STATUS and WAKE_INFO
#define PWRMGR_PARAM_PINMUX_AON_PIN_WKUP_REQ_IDX 1

// Vector index for pinmux_aon usb_wkup_req, applies for WAKEUP_EN,
// WAKE_STATUS and WAKE_INFO
#define PWRMGR_PARAM_PINMUX_AON_USB_WKUP_REQ_IDX 2

// Vector index for aon_timer_aon wkup_req, applies for WAKEUP_EN,
// WAKE_STATUS and WAKE_INFO
#define PWRMGR_PARAM_AON_TIMER_AON_WKUP_REQ_IDX 3

// Number of peripheral reset requets
#define PWRMGR_PARAM_NUM_RST_REQS 2

// Number of pwrmgr internal reset requets
#define PWRMGR_PARAM_NUM_INT_RST_REQS 2

// Number of debug reset requets
#define PWRMGR_PARAM_NUM_DEBUG_RST_REQS 1

// Reset req idx for MainPwr
#define PWRMGR_PARAM_RESET_MAIN_PWR_IDX 2

// Reset req idx for Esc
#define PWRMGR_PARAM_RESET_ESC_IDX 3

// Reset req idx for Ndm
#define PWRMGR_PARAM_RESET_NDM_IDX 4

// Number of alerts
#define PWRMGR_PARAM_NUM_ALERTS 1

// Register width
#define PWRMGR_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define PWRMGR_INTR_COMMON_WAKEUP_BIT 0

// Interrupt State Register
#define PWRMGR_INTR_STATE_REG_OFFSET 0x0
#define PWRMGR_INTR_STATE_REG_RESVAL 0x0
#define PWRMGR_INTR_STATE_WAKEUP_BIT 0

// Interrupt Enable Register
#define PWRMGR_INTR_ENABLE_REG_OFFSET 0x4
#define PWRMGR_INTR_ENABLE_REG_RESVAL 0x0
#define PWRMGR_INTR_ENABLE_WAKEUP_BIT 0

// Interrupt Test Register
#define PWRMGR_INTR_TEST_REG_OFFSET 0x8
#define PWRMGR_INTR_TEST_REG_RESVAL 0x0
#define PWRMGR_INTR_TEST_WAKEUP_BIT 0

// Alert Test Register
#define PWRMGR_ALERT_TEST_REG_OFFSET 0xc
#define PWRMGR_ALERT_TEST_REG_RESVAL 0x0
#define PWRMGR_ALERT_TEST_FATAL_FAULT_BIT 0

// Controls the configurability of the !!CONTROL register.
#define PWRMGR_CTRL_CFG_REGWEN_REG_OFFSET 0x10
#define PWRMGR_CTRL_CFG_REGWEN_REG_RESVAL 0x1
#define PWRMGR_CTRL_CFG_REGWEN_EN_BIT 0

// Control register
#define PWRMGR_CONTROL_REG_OFFSET 0x14
#define PWRMGR_CONTROL_REG_RESVAL 0x180
#define PWRMGR_CONTROL_LOW_POWER_HINT_BIT 0
#define PWRMGR_CONTROL_CORE_CLK_EN_BIT 4
#define PWRMGR_CONTROL_IO_CLK_EN_BIT 5
#define PWRMGR_CONTROL_USB_CLK_EN_LP_BIT 6
#define PWRMGR_CONTROL_USB_CLK_EN_ACTIVE_BIT 7
#define PWRMGR_CONTROL_MAIN_PD_N_BIT 8

// The configuration registers CONTROL, WAKEUP_EN, RESET_EN are all written
// in the
#define PWRMGR_CFG_CDC_SYNC_REG_OFFSET 0x18
#define PWRMGR_CFG_CDC_SYNC_REG_RESVAL 0x0
#define PWRMGR_CFG_CDC_SYNC_SYNC_BIT 0

// Configuration enable for wakeup_en register
#define PWRMGR_WAKEUP_EN_REGWEN_REG_OFFSET 0x1c
#define PWRMGR_WAKEUP_EN_REGWEN_REG_RESVAL 0x1
#define PWRMGR_WAKEUP_EN_REGWEN_EN_BIT 0

// Bit mask for enabled wakeups (common parameters)
#define PWRMGR_WAKEUP_EN_EN_FIELD_WIDTH 1
#define PWRMGR_WAKEUP_EN_MULTIREG_COUNT 1

// Bit mask for enabled wakeups
#define PWRMGR_WAKEUP_EN_REG_OFFSET 0x20
#define PWRMGR_WAKEUP_EN_REG_RESVAL 0x0
#define PWRMGR_WAKEUP_EN_EN_0_BIT 0
#define PWRMGR_WAKEUP_EN_EN_1_BIT 1
#define PWRMGR_WAKEUP_EN_EN_2_BIT 2
#define PWRMGR_WAKEUP_EN_EN_3_BIT 3

// A read only register of all current wake requests post enable mask (common
// parameters)
#define PWRMGR_WAKE_STATUS_VAL_FIELD_WIDTH 1
#define PWRMGR_WAKE_STATUS_MULTIREG_COUNT 1

// A read only register of all current wake requests post enable mask
#define PWRMGR_WAKE_STATUS_REG_OFFSET 0x24
#define PWRMGR_WAKE_STATUS_REG_RESVAL 0x0
#define PWRMGR_WAKE_STATUS_VAL_0_BIT 0
#define PWRMGR_WAKE_STATUS_VAL_1_BIT 1
#define PWRMGR_WAKE_STATUS_VAL_2_BIT 2
#define PWRMGR_WAKE_STATUS_VAL_3_BIT 3

// Configuration enable for reset_en register
#define PWRMGR_RESET_EN_REGWEN_REG_OFFSET 0x28
#define PWRMGR_RESET_EN_REGWEN_REG_RESVAL 0x1
#define PWRMGR_RESET_EN_REGWEN_EN_BIT 0

// Bit mask for enabled reset requests (common parameters)
#define PWRMGR_RESET_EN_EN_FIELD_WIDTH 1
#define PWRMGR_RESET_EN_MULTIREG_COUNT 1

// Bit mask for enabled reset requests
#define PWRMGR_RESET_EN_REG_OFFSET 0x2c
#define PWRMGR_RESET_EN_REG_RESVAL 0x0
#define PWRMGR_RESET_EN_EN_0_BIT 0
#define PWRMGR_RESET_EN_EN_1_BIT 1

// A read only register of all current reset requests post enable mask
// (common parameters)
#define PWRMGR_RESET_STATUS_VAL_FIELD_WIDTH 1
#define PWRMGR_RESET_STATUS_MULTIREG_COUNT 1

// A read only register of all current reset requests post enable mask
#define PWRMGR_RESET_STATUS_REG_OFFSET 0x30
#define PWRMGR_RESET_STATUS_REG_RESVAL 0x0
#define PWRMGR_RESET_STATUS_VAL_0_BIT 0
#define PWRMGR_RESET_STATUS_VAL_1_BIT 1

// A read only register of escalation reset request
#define PWRMGR_ESCALATE_RESET_STATUS_REG_OFFSET 0x34
#define PWRMGR_ESCALATE_RESET_STATUS_REG_RESVAL 0x0
#define PWRMGR_ESCALATE_RESET_STATUS_VAL_BIT 0

// Indicates which functions caused the chip to wakeup
#define PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_OFFSET 0x38
#define PWRMGR_WAKE_INFO_CAPTURE_DIS_REG_RESVAL 0x0
#define PWRMGR_WAKE_INFO_CAPTURE_DIS_VAL_BIT 0

// Indicates which functions caused the chip to wakeup.
#define PWRMGR_WAKE_INFO_REG_OFFSET 0x3c
#define PWRMGR_WAKE_INFO_REG_RESVAL 0x0
#define PWRMGR_WAKE_INFO_REASONS_MASK 0xf
#define PWRMGR_WAKE_INFO_REASONS_OFFSET 0
#define PWRMGR_WAKE_INFO_REASONS_FIELD \
  ((bitfield_field32_t) { .mask = PWRMGR_WAKE_INFO_REASONS_MASK, .index = PWRMGR_WAKE_INFO_REASONS_OFFSET })
#define PWRMGR_WAKE_INFO_FALL_THROUGH_BIT 4
#define PWRMGR_WAKE_INFO_ABORT_BIT 5

// A read only register that shows the existing faults
#define PWRMGR_FAULT_STATUS_REG_OFFSET 0x40
#define PWRMGR_FAULT_STATUS_REG_RESVAL 0x0
#define PWRMGR_FAULT_STATUS_REG_INTG_ERR_BIT 0
#define PWRMGR_FAULT_STATUS_ESC_TIMEOUT_BIT 1
#define PWRMGR_FAULT_STATUS_MAIN_PD_GLITCH_BIT 2

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _PWRMGR_REG_DEFS_
// End generated register defines for PWRMGR