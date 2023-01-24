// Generated register defines for edn

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _EDN_REG_DEFS_
#define _EDN_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of alerts
#define EDN_PARAM_NUM_ALERTS 2

// Register width
#define EDN_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define EDN_INTR_COMMON_EDN_CMD_REQ_DONE_BIT 0
#define EDN_INTR_COMMON_EDN_FATAL_ERR_BIT 1

// Interrupt State Register
#define EDN_INTR_STATE_REG_OFFSET 0x0
#define EDN_INTR_STATE_REG_RESVAL 0x0
#define EDN_INTR_STATE_EDN_CMD_REQ_DONE_BIT 0
#define EDN_INTR_STATE_EDN_FATAL_ERR_BIT 1

// Interrupt Enable Register
#define EDN_INTR_ENABLE_REG_OFFSET 0x4
#define EDN_INTR_ENABLE_REG_RESVAL 0x0
#define EDN_INTR_ENABLE_EDN_CMD_REQ_DONE_BIT 0
#define EDN_INTR_ENABLE_EDN_FATAL_ERR_BIT 1

// Interrupt Test Register
#define EDN_INTR_TEST_REG_OFFSET 0x8
#define EDN_INTR_TEST_REG_RESVAL 0x0
#define EDN_INTR_TEST_EDN_CMD_REQ_DONE_BIT 0
#define EDN_INTR_TEST_EDN_FATAL_ERR_BIT 1

// Alert Test Register
#define EDN_ALERT_TEST_REG_OFFSET 0xc
#define EDN_ALERT_TEST_REG_RESVAL 0x0
#define EDN_ALERT_TEST_RECOV_ALERT_BIT 0
#define EDN_ALERT_TEST_FATAL_ALERT_BIT 1

// Register write enable for all control registers
#define EDN_REGWEN_REG_OFFSET 0x10
#define EDN_REGWEN_REG_RESVAL 0x1
#define EDN_REGWEN_REGWEN_BIT 0

// EDN control register
#define EDN_CTRL_REG_OFFSET 0x14
#define EDN_CTRL_REG_RESVAL 0x9999
#define EDN_CTRL_EDN_ENABLE_MASK 0xf
#define EDN_CTRL_EDN_ENABLE_OFFSET 0
#define EDN_CTRL_EDN_ENABLE_FIELD \
  ((bitfield_field32_t) { .mask = EDN_CTRL_EDN_ENABLE_MASK, .index = EDN_CTRL_EDN_ENABLE_OFFSET })
#define EDN_CTRL_BOOT_REQ_MODE_MASK 0xf
#define EDN_CTRL_BOOT_REQ_MODE_OFFSET 4
#define EDN_CTRL_BOOT_REQ_MODE_FIELD \
  ((bitfield_field32_t) { .mask = EDN_CTRL_BOOT_REQ_MODE_MASK, .index = EDN_CTRL_BOOT_REQ_MODE_OFFSET })
#define EDN_CTRL_AUTO_REQ_MODE_MASK 0xf
#define EDN_CTRL_AUTO_REQ_MODE_OFFSET 8
#define EDN_CTRL_AUTO_REQ_MODE_FIELD \
  ((bitfield_field32_t) { .mask = EDN_CTRL_AUTO_REQ_MODE_MASK, .index = EDN_CTRL_AUTO_REQ_MODE_OFFSET })
#define EDN_CTRL_CMD_FIFO_RST_MASK 0xf
#define EDN_CTRL_CMD_FIFO_RST_OFFSET 12
#define EDN_CTRL_CMD_FIFO_RST_FIELD \
  ((bitfield_field32_t) { .mask = EDN_CTRL_CMD_FIFO_RST_MASK, .index = EDN_CTRL_CMD_FIFO_RST_OFFSET })

// EDN boot instantiate command register
#define EDN_BOOT_INS_CMD_REG_OFFSET 0x18
#define EDN_BOOT_INS_CMD_REG_RESVAL 0x901

// EDN boot generate command register
#define EDN_BOOT_GEN_CMD_REG_OFFSET 0x1c
#define EDN_BOOT_GEN_CMD_REG_RESVAL 0xfff003

// EDN csrng app command request register
#define EDN_SW_CMD_REQ_REG_OFFSET 0x20
#define EDN_SW_CMD_REQ_REG_RESVAL 0x0

// EDN command status register
#define EDN_SW_CMD_STS_REG_OFFSET 0x24
#define EDN_SW_CMD_STS_REG_RESVAL 0x0
#define EDN_SW_CMD_STS_CMD_RDY_BIT 0
#define EDN_SW_CMD_STS_CMD_STS_BIT 1

// EDN csrng reseed command register
#define EDN_RESEED_CMD_REG_OFFSET 0x28
#define EDN_RESEED_CMD_REG_RESVAL 0x0

// EDN csrng generate command register
#define EDN_GENERATE_CMD_REG_OFFSET 0x2c
#define EDN_GENERATE_CMD_REG_RESVAL 0x0

// EDN maximum number of requests between reseeds register
#define EDN_MAX_NUM_REQS_BETWEEN_RESEEDS_REG_OFFSET 0x30
#define EDN_MAX_NUM_REQS_BETWEEN_RESEEDS_REG_RESVAL 0x0

// Recoverable alert status register
#define EDN_RECOV_ALERT_STS_REG_OFFSET 0x34
#define EDN_RECOV_ALERT_STS_REG_RESVAL 0x0
#define EDN_RECOV_ALERT_STS_EDN_ENABLE_FIELD_ALERT_BIT 0
#define EDN_RECOV_ALERT_STS_BOOT_REQ_MODE_FIELD_ALERT_BIT 1
#define EDN_RECOV_ALERT_STS_AUTO_REQ_MODE_FIELD_ALERT_BIT 2
#define EDN_RECOV_ALERT_STS_CMD_FIFO_RST_FIELD_ALERT_BIT 3
#define EDN_RECOV_ALERT_STS_EDN_BUS_CMP_ALERT_BIT 12

// Hardware detection of fatal error conditions status register
#define EDN_ERR_CODE_REG_OFFSET 0x38
#define EDN_ERR_CODE_REG_RESVAL 0x0
#define EDN_ERR_CODE_SFIFO_RESCMD_ERR_BIT 0
#define EDN_ERR_CODE_SFIFO_GENCMD_ERR_BIT 1
#define EDN_ERR_CODE_SFIFO_OUTPUT_ERR_BIT 2
#define EDN_ERR_CODE_EDN_ACK_SM_ERR_BIT 20
#define EDN_ERR_CODE_EDN_MAIN_SM_ERR_BIT 21
#define EDN_ERR_CODE_EDN_CNTR_ERR_BIT 22
#define EDN_ERR_CODE_FIFO_WRITE_ERR_BIT 28
#define EDN_ERR_CODE_FIFO_READ_ERR_BIT 29
#define EDN_ERR_CODE_FIFO_STATE_ERR_BIT 30

// Test error conditions register
#define EDN_ERR_CODE_TEST_REG_OFFSET 0x3c
#define EDN_ERR_CODE_TEST_REG_RESVAL 0x0
#define EDN_ERR_CODE_TEST_ERR_CODE_TEST_MASK 0x1f
#define EDN_ERR_CODE_TEST_ERR_CODE_TEST_OFFSET 0
#define EDN_ERR_CODE_TEST_ERR_CODE_TEST_FIELD \
  ((bitfield_field32_t) { .mask = EDN_ERR_CODE_TEST_ERR_CODE_TEST_MASK, .index = EDN_ERR_CODE_TEST_ERR_CODE_TEST_OFFSET })

// Main state machine state debug register
#define EDN_MAIN_SM_STATE_REG_OFFSET 0x40
#define EDN_MAIN_SM_STATE_REG_RESVAL 0x185
#define EDN_MAIN_SM_STATE_MAIN_SM_STATE_MASK 0x1ff
#define EDN_MAIN_SM_STATE_MAIN_SM_STATE_OFFSET 0
#define EDN_MAIN_SM_STATE_MAIN_SM_STATE_FIELD \
  ((bitfield_field32_t) { .mask = EDN_MAIN_SM_STATE_MAIN_SM_STATE_MASK, .index = EDN_MAIN_SM_STATE_MAIN_SM_STATE_OFFSET })

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _EDN_REG_DEFS_
// End generated register defines for edn