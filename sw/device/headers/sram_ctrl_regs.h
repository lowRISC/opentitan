// Generated register defines for sram_ctrl

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _SRAM_CTRL_REG_DEFS_
#define _SRAM_CTRL_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of alerts
#define SRAM_CTRL_PARAM_NUM_ALERTS 1

// Register width
#define SRAM_CTRL_PARAM_REG_WIDTH 32

// Alert Test Register
#define SRAM_CTRL_ALERT_TEST_REG_OFFSET 0x0
#define SRAM_CTRL_ALERT_TEST_REG_RESVAL 0x0
#define SRAM_CTRL_ALERT_TEST_FATAL_ERROR_BIT 0

// SRAM status register.
#define SRAM_CTRL_STATUS_REG_OFFSET 0x4
#define SRAM_CTRL_STATUS_REG_RESVAL 0x0
#define SRAM_CTRL_STATUS_BUS_INTEG_ERROR_BIT 0
#define SRAM_CTRL_STATUS_INIT_ERROR_BIT 1
#define SRAM_CTRL_STATUS_ESCALATED_BIT 2
#define SRAM_CTRL_STATUS_SCR_KEY_VALID_BIT 3
#define SRAM_CTRL_STATUS_SCR_KEY_SEED_VALID_BIT 4
#define SRAM_CTRL_STATUS_INIT_DONE_BIT 5

// Lock register for execution enable register.
#define SRAM_CTRL_EXEC_REGWEN_REG_OFFSET 0x8
#define SRAM_CTRL_EXEC_REGWEN_REG_RESVAL 0x1
#define SRAM_CTRL_EXEC_REGWEN_EXEC_REGWEN_BIT 0

// Sram execution enable.
#define SRAM_CTRL_EXEC_REG_OFFSET 0xc
#define SRAM_CTRL_EXEC_REG_RESVAL 0x9
#define SRAM_CTRL_EXEC_EN_MASK 0xf
#define SRAM_CTRL_EXEC_EN_OFFSET 0
#define SRAM_CTRL_EXEC_EN_FIELD \
  ((bitfield_field32_t) { .mask = SRAM_CTRL_EXEC_EN_MASK, .index = SRAM_CTRL_EXEC_EN_OFFSET })

// Lock register for control register.
#define SRAM_CTRL_CTRL_REGWEN_REG_OFFSET 0x10
#define SRAM_CTRL_CTRL_REGWEN_REG_RESVAL 0x1
#define SRAM_CTRL_CTRL_REGWEN_CTRL_REGWEN_BIT 0

// SRAM ctrl register.
#define SRAM_CTRL_CTRL_REG_OFFSET 0x14
#define SRAM_CTRL_CTRL_REG_RESVAL 0x0
#define SRAM_CTRL_CTRL_RENEW_SCR_KEY_BIT 0
#define SRAM_CTRL_CTRL_INIT_BIT 1

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _SRAM_CTRL_REG_DEFS_
// End generated register defines for sram_ctrl