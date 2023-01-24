// Generated register defines for otbn

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _OTBN_REG_DEFS_
#define _OTBN_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of alerts
#define OTBN_PARAM_NUM_ALERTS 2

// Register width
#define OTBN_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define OTBN_INTR_COMMON_DONE_BIT 0

// Interrupt State Register
#define OTBN_INTR_STATE_REG_OFFSET 0x0
#define OTBN_INTR_STATE_REG_RESVAL 0x0
#define OTBN_INTR_STATE_DONE_BIT 0

// Interrupt Enable Register
#define OTBN_INTR_ENABLE_REG_OFFSET 0x4
#define OTBN_INTR_ENABLE_REG_RESVAL 0x0
#define OTBN_INTR_ENABLE_DONE_BIT 0

// Interrupt Test Register
#define OTBN_INTR_TEST_REG_OFFSET 0x8
#define OTBN_INTR_TEST_REG_RESVAL 0x0
#define OTBN_INTR_TEST_DONE_BIT 0

// Alert Test Register
#define OTBN_ALERT_TEST_REG_OFFSET 0xc
#define OTBN_ALERT_TEST_REG_RESVAL 0x0
#define OTBN_ALERT_TEST_FATAL_BIT 0
#define OTBN_ALERT_TEST_RECOV_BIT 1

// Command Register
#define OTBN_CMD_REG_OFFSET 0x10
#define OTBN_CMD_REG_RESVAL 0x0
#define OTBN_CMD_CMD_MASK 0xff
#define OTBN_CMD_CMD_OFFSET 0
#define OTBN_CMD_CMD_FIELD \
  ((bitfield_field32_t) { .mask = OTBN_CMD_CMD_MASK, .index = OTBN_CMD_CMD_OFFSET })

// Control Register
#define OTBN_CTRL_REG_OFFSET 0x14
#define OTBN_CTRL_REG_RESVAL 0x0
#define OTBN_CTRL_SOFTWARE_ERRS_FATAL_BIT 0

// Status Register
#define OTBN_STATUS_REG_OFFSET 0x18
#define OTBN_STATUS_REG_RESVAL 0x4
#define OTBN_STATUS_STATUS_MASK 0xff
#define OTBN_STATUS_STATUS_OFFSET 0
#define OTBN_STATUS_STATUS_FIELD \
  ((bitfield_field32_t) { .mask = OTBN_STATUS_STATUS_MASK, .index = OTBN_STATUS_STATUS_OFFSET })

// Operation Result Register
#define OTBN_ERR_BITS_REG_OFFSET 0x1c
#define OTBN_ERR_BITS_REG_RESVAL 0x0
#define OTBN_ERR_BITS_BAD_DATA_ADDR_BIT 0
#define OTBN_ERR_BITS_BAD_INSN_ADDR_BIT 1
#define OTBN_ERR_BITS_CALL_STACK_BIT 2
#define OTBN_ERR_BITS_ILLEGAL_INSN_BIT 3
#define OTBN_ERR_BITS_LOOP_BIT 4
#define OTBN_ERR_BITS_KEY_INVALID_BIT 5
#define OTBN_ERR_BITS_RND_REP_CHK_FAIL_BIT 6
#define OTBN_ERR_BITS_RND_FIPS_CHK_FAIL_BIT 7
#define OTBN_ERR_BITS_IMEM_INTG_VIOLATION_BIT 16
#define OTBN_ERR_BITS_DMEM_INTG_VIOLATION_BIT 17
#define OTBN_ERR_BITS_REG_INTG_VIOLATION_BIT 18
#define OTBN_ERR_BITS_BUS_INTG_VIOLATION_BIT 19
#define OTBN_ERR_BITS_BAD_INTERNAL_STATE_BIT 20
#define OTBN_ERR_BITS_ILLEGAL_BUS_ACCESS_BIT 21
#define OTBN_ERR_BITS_LIFECYCLE_ESCALATION_BIT 22
#define OTBN_ERR_BITS_FATAL_SOFTWARE_BIT 23

// Fatal Alert Cause Register
#define OTBN_FATAL_ALERT_CAUSE_REG_OFFSET 0x20
#define OTBN_FATAL_ALERT_CAUSE_REG_RESVAL 0x0
#define OTBN_FATAL_ALERT_CAUSE_IMEM_INTG_VIOLATION_BIT 0
#define OTBN_FATAL_ALERT_CAUSE_DMEM_INTG_VIOLATION_BIT 1
#define OTBN_FATAL_ALERT_CAUSE_REG_INTG_VIOLATION_BIT 2
#define OTBN_FATAL_ALERT_CAUSE_BUS_INTG_VIOLATION_BIT 3
#define OTBN_FATAL_ALERT_CAUSE_BAD_INTERNAL_STATE_BIT 4
#define OTBN_FATAL_ALERT_CAUSE_ILLEGAL_BUS_ACCESS_BIT 5
#define OTBN_FATAL_ALERT_CAUSE_LIFECYCLE_ESCALATION_BIT 6
#define OTBN_FATAL_ALERT_CAUSE_FATAL_SOFTWARE_BIT 7

// Instruction Count Register
#define OTBN_INSN_CNT_REG_OFFSET 0x24
#define OTBN_INSN_CNT_REG_RESVAL 0x0

// A 32-bit CRC checksum of data written to memory
#define OTBN_LOAD_CHECKSUM_REG_OFFSET 0x28
#define OTBN_LOAD_CHECKSUM_REG_RESVAL 0x0

// Memory area: Instruction Memory Access
#define OTBN_IMEM_REG_OFFSET 0x4000
#define OTBN_IMEM_SIZE_WORDS 1024
#define OTBN_IMEM_SIZE_BYTES 4096
// Memory area: Data Memory Access
#define OTBN_DMEM_REG_OFFSET 0x8000
#define OTBN_DMEM_SIZE_WORDS 768
#define OTBN_DMEM_SIZE_BYTES 3072
#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _OTBN_REG_DEFS_
// End generated register defines for otbn