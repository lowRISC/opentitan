// Generated register defines for RSTMGR

// Copyright information found in source file:
// Copyright lowRISC contributors.Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _RSTMGR_REG_DEFS_
#define _RSTMGR_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Read width for crash info
#define RSTMGR_PARAM_RD_WIDTH 32

// Index width for crash info
#define RSTMGR_PARAM_IDX_WIDTH 4

// Number of hardware reset requests, inclusive of debug resets and pwrmgr's
// internal resets
#define RSTMGR_PARAM_NUM_HW_RESETS 5

// Number of software resets
#define RSTMGR_PARAM_NUM_SW_RESETS 8

// Number of total reset requests, inclusive of hw/sw, por and low power exit
#define RSTMGR_PARAM_NUM_TOTAL_RESETS 8

// Number of alerts
#define RSTMGR_PARAM_NUM_ALERTS 2

// Register width
#define RSTMGR_PARAM_REG_WIDTH 32

// Alert Test Register
#define RSTMGR_ALERT_TEST_REG_OFFSET 0x0
#define RSTMGR_ALERT_TEST_REG_RESVAL 0x0
#define RSTMGR_ALERT_TEST_FATAL_FAULT_BIT 0
#define RSTMGR_ALERT_TEST_FATAL_CNSTY_FAULT_BIT 1

// Software requested system reset.
#define RSTMGR_RESET_REQ_REG_OFFSET 0x4
#define RSTMGR_RESET_REQ_REG_RESVAL 0x9
#define RSTMGR_RESET_REQ_VAL_MASK 0xf
#define RSTMGR_RESET_REQ_VAL_OFFSET 0
#define RSTMGR_RESET_REQ_VAL_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_RESET_REQ_VAL_MASK, .index = RSTMGR_RESET_REQ_VAL_OFFSET })

// Device reset reason.
#define RSTMGR_RESET_INFO_REG_OFFSET 0x8
#define RSTMGR_RESET_INFO_REG_RESVAL 0x1
#define RSTMGR_RESET_INFO_POR_BIT 0
#define RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT 1
#define RSTMGR_RESET_INFO_SW_RESET_BIT 2
#define RSTMGR_RESET_INFO_HW_REQ_MASK 0x1f
#define RSTMGR_RESET_INFO_HW_REQ_OFFSET 3
#define RSTMGR_RESET_INFO_HW_REQ_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_RESET_INFO_HW_REQ_MASK, .index = RSTMGR_RESET_INFO_HW_REQ_OFFSET })

// Alert write enable
#define RSTMGR_ALERT_REGWEN_REG_OFFSET 0xc
#define RSTMGR_ALERT_REGWEN_REG_RESVAL 0x1
#define RSTMGR_ALERT_REGWEN_EN_BIT 0

// Alert info dump controls.
#define RSTMGR_ALERT_INFO_CTRL_REG_OFFSET 0x10
#define RSTMGR_ALERT_INFO_CTRL_REG_RESVAL 0x0
#define RSTMGR_ALERT_INFO_CTRL_EN_BIT 0
#define RSTMGR_ALERT_INFO_CTRL_INDEX_MASK 0xf
#define RSTMGR_ALERT_INFO_CTRL_INDEX_OFFSET 4
#define RSTMGR_ALERT_INFO_CTRL_INDEX_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_ALERT_INFO_CTRL_INDEX_MASK, .index = RSTMGR_ALERT_INFO_CTRL_INDEX_OFFSET })

// Alert info dump attributes.
#define RSTMGR_ALERT_INFO_ATTR_REG_OFFSET 0x14
#define RSTMGR_ALERT_INFO_ATTR_REG_RESVAL 0x0
#define RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_MASK 0xf
#define RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_OFFSET 0
#define RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_MASK, .index = RSTMGR_ALERT_INFO_ATTR_CNT_AVAIL_OFFSET })

//   Alert dump information prior to last reset.
#define RSTMGR_ALERT_INFO_REG_OFFSET 0x18
#define RSTMGR_ALERT_INFO_REG_RESVAL 0x0

// Cpu write enable
#define RSTMGR_CPU_REGWEN_REG_OFFSET 0x1c
#define RSTMGR_CPU_REGWEN_REG_RESVAL 0x1
#define RSTMGR_CPU_REGWEN_EN_BIT 0

// Cpu info dump controls.
#define RSTMGR_CPU_INFO_CTRL_REG_OFFSET 0x20
#define RSTMGR_CPU_INFO_CTRL_REG_RESVAL 0x0
#define RSTMGR_CPU_INFO_CTRL_EN_BIT 0
#define RSTMGR_CPU_INFO_CTRL_INDEX_MASK 0xf
#define RSTMGR_CPU_INFO_CTRL_INDEX_OFFSET 4
#define RSTMGR_CPU_INFO_CTRL_INDEX_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_CPU_INFO_CTRL_INDEX_MASK, .index = RSTMGR_CPU_INFO_CTRL_INDEX_OFFSET })

// Cpu info dump attributes.
#define RSTMGR_CPU_INFO_ATTR_REG_OFFSET 0x24
#define RSTMGR_CPU_INFO_ATTR_REG_RESVAL 0x0
#define RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_MASK 0xf
#define RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_OFFSET 0
#define RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_FIELD \
  ((bitfield_field32_t) { .mask = RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_MASK, .index = RSTMGR_CPU_INFO_ATTR_CNT_AVAIL_OFFSET })

//   Cpu dump information prior to last reset.
#define RSTMGR_CPU_INFO_REG_OFFSET 0x28
#define RSTMGR_CPU_INFO_REG_RESVAL 0x0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_EN_FIELD_WIDTH 1
#define RSTMGR_SW_RST_REGWEN_MULTIREG_COUNT 8

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_0_REG_OFFSET 0x2c
#define RSTMGR_SW_RST_REGWEN_0_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_0_EN_0_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_1_REG_OFFSET 0x30
#define RSTMGR_SW_RST_REGWEN_1_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_1_EN_1_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_2_REG_OFFSET 0x34
#define RSTMGR_SW_RST_REGWEN_2_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_2_EN_2_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_3_REG_OFFSET 0x38
#define RSTMGR_SW_RST_REGWEN_3_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_3_EN_3_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_4_REG_OFFSET 0x3c
#define RSTMGR_SW_RST_REGWEN_4_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_4_EN_4_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_5_REG_OFFSET 0x40
#define RSTMGR_SW_RST_REGWEN_5_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_5_EN_5_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_6_REG_OFFSET 0x44
#define RSTMGR_SW_RST_REGWEN_6_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_6_EN_6_BIT 0

// Register write enable for software controllable resets.
#define RSTMGR_SW_RST_REGWEN_7_REG_OFFSET 0x48
#define RSTMGR_SW_RST_REGWEN_7_REG_RESVAL 0x1
#define RSTMGR_SW_RST_REGWEN_7_EN_7_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_VAL_FIELD_WIDTH 1
#define RSTMGR_SW_RST_CTRL_N_MULTIREG_COUNT 8

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET 0x4c
#define RSTMGR_SW_RST_CTRL_N_0_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_0_VAL_0_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_1_REG_OFFSET 0x50
#define RSTMGR_SW_RST_CTRL_N_1_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_1_VAL_1_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_2_REG_OFFSET 0x54
#define RSTMGR_SW_RST_CTRL_N_2_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_2_VAL_2_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_3_REG_OFFSET 0x58
#define RSTMGR_SW_RST_CTRL_N_3_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_3_VAL_3_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_4_REG_OFFSET 0x5c
#define RSTMGR_SW_RST_CTRL_N_4_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_4_VAL_4_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_5_REG_OFFSET 0x60
#define RSTMGR_SW_RST_CTRL_N_5_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_5_VAL_5_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_6_REG_OFFSET 0x64
#define RSTMGR_SW_RST_CTRL_N_6_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_6_VAL_6_BIT 0

// Software controllable resets.
#define RSTMGR_SW_RST_CTRL_N_7_REG_OFFSET 0x68
#define RSTMGR_SW_RST_CTRL_N_7_REG_RESVAL 0x1
#define RSTMGR_SW_RST_CTRL_N_7_VAL_7_BIT 0

// A bit vector of all the errors that have occurred in reset manager
#define RSTMGR_ERR_CODE_REG_OFFSET 0x6c
#define RSTMGR_ERR_CODE_REG_RESVAL 0x0
#define RSTMGR_ERR_CODE_REG_INTG_ERR_BIT 0
#define RSTMGR_ERR_CODE_RESET_CONSISTENCY_ERR_BIT 1
#define RSTMGR_ERR_CODE_FSM_ERR_BIT 2

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _RSTMGR_REG_DEFS_
// End generated register defines for RSTMGR