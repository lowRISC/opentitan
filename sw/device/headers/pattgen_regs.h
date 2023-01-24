// Generated register defines for pattgen

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _PATTGEN_REG_DEFS_
#define _PATTGEN_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of data registers per each channel
#define PATTGEN_PARAM_NUM_REGS_DATA 2

// Number of alerts
#define PATTGEN_PARAM_NUM_ALERTS 1

// Register width
#define PATTGEN_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define PATTGEN_INTR_COMMON_DONE_CH0_BIT 0
#define PATTGEN_INTR_COMMON_DONE_CH1_BIT 1

// Interrupt State Register
#define PATTGEN_INTR_STATE_REG_OFFSET 0x0
#define PATTGEN_INTR_STATE_REG_RESVAL 0x0
#define PATTGEN_INTR_STATE_DONE_CH0_BIT 0
#define PATTGEN_INTR_STATE_DONE_CH1_BIT 1

// Interrupt Enable Register
#define PATTGEN_INTR_ENABLE_REG_OFFSET 0x4
#define PATTGEN_INTR_ENABLE_REG_RESVAL 0x0
#define PATTGEN_INTR_ENABLE_DONE_CH0_BIT 0
#define PATTGEN_INTR_ENABLE_DONE_CH1_BIT 1

// Interrupt Test Register
#define PATTGEN_INTR_TEST_REG_OFFSET 0x8
#define PATTGEN_INTR_TEST_REG_RESVAL 0x0
#define PATTGEN_INTR_TEST_DONE_CH0_BIT 0
#define PATTGEN_INTR_TEST_DONE_CH1_BIT 1

// Alert Test Register
#define PATTGEN_ALERT_TEST_REG_OFFSET 0xc
#define PATTGEN_ALERT_TEST_REG_RESVAL 0x0
#define PATTGEN_ALERT_TEST_FATAL_FAULT_BIT 0

// PATTGEN control register
#define PATTGEN_CTRL_REG_OFFSET 0x10
#define PATTGEN_CTRL_REG_RESVAL 0x0
#define PATTGEN_CTRL_ENABLE_CH0_BIT 0
#define PATTGEN_CTRL_ENABLE_CH1_BIT 1
#define PATTGEN_CTRL_POLARITY_CH0_BIT 2
#define PATTGEN_CTRL_POLARITY_CH1_BIT 3

// PATTGEN pre-divider register for Channel 0
#define PATTGEN_PREDIV_CH0_REG_OFFSET 0x14
#define PATTGEN_PREDIV_CH0_REG_RESVAL 0x0

// PATTGEN pre-divider register for Channel 1
#define PATTGEN_PREDIV_CH1_REG_OFFSET 0x18
#define PATTGEN_PREDIV_CH1_REG_RESVAL 0x0

// PATTGEN seed pattern multi-registers for Channel 0. (common parameters)
#define PATTGEN_DATA_CH0_DATA_FIELD_WIDTH 32
#define PATTGEN_DATA_CH0_MULTIREG_COUNT 2

// PATTGEN seed pattern multi-registers for Channel 0.
#define PATTGEN_DATA_CH0_0_REG_OFFSET 0x1c
#define PATTGEN_DATA_CH0_0_REG_RESVAL 0x0

// PATTGEN seed pattern multi-registers for Channel 0.
#define PATTGEN_DATA_CH0_1_REG_OFFSET 0x20
#define PATTGEN_DATA_CH0_1_REG_RESVAL 0x0

// PATTGEN seed pattern multi-registers for Channel 1. (common parameters)
#define PATTGEN_DATA_CH1_DATA_FIELD_WIDTH 32
#define PATTGEN_DATA_CH1_MULTIREG_COUNT 2

// PATTGEN seed pattern multi-registers for Channel 1.
#define PATTGEN_DATA_CH1_0_REG_OFFSET 0x24
#define PATTGEN_DATA_CH1_0_REG_RESVAL 0x0

// PATTGEN seed pattern multi-registers for Channel 1.
#define PATTGEN_DATA_CH1_1_REG_OFFSET 0x28
#define PATTGEN_DATA_CH1_1_REG_RESVAL 0x0

// PATTGEN pattern length
#define PATTGEN_SIZE_REG_OFFSET 0x2c
#define PATTGEN_SIZE_REG_RESVAL 0x0
#define PATTGEN_SIZE_LEN_CH0_MASK 0x3f
#define PATTGEN_SIZE_LEN_CH0_OFFSET 0
#define PATTGEN_SIZE_LEN_CH0_FIELD \
  ((bitfield_field32_t) { .mask = PATTGEN_SIZE_LEN_CH0_MASK, .index = PATTGEN_SIZE_LEN_CH0_OFFSET })
#define PATTGEN_SIZE_REPS_CH0_MASK 0x3ff
#define PATTGEN_SIZE_REPS_CH0_OFFSET 6
#define PATTGEN_SIZE_REPS_CH0_FIELD \
  ((bitfield_field32_t) { .mask = PATTGEN_SIZE_REPS_CH0_MASK, .index = PATTGEN_SIZE_REPS_CH0_OFFSET })
#define PATTGEN_SIZE_LEN_CH1_MASK 0x3f
#define PATTGEN_SIZE_LEN_CH1_OFFSET 16
#define PATTGEN_SIZE_LEN_CH1_FIELD \
  ((bitfield_field32_t) { .mask = PATTGEN_SIZE_LEN_CH1_MASK, .index = PATTGEN_SIZE_LEN_CH1_OFFSET })
#define PATTGEN_SIZE_REPS_CH1_MASK 0x3ff
#define PATTGEN_SIZE_REPS_CH1_OFFSET 22
#define PATTGEN_SIZE_REPS_CH1_FIELD \
  ((bitfield_field32_t) { .mask = PATTGEN_SIZE_REPS_CH1_MASK, .index = PATTGEN_SIZE_REPS_CH1_OFFSET })

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _PATTGEN_REG_DEFS_
// End generated register defines for pattgen