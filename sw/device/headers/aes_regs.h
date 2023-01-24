// Generated register defines for aes

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _AES_REG_DEFS_
#define _AES_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number registers for key
#define AES_PARAM_NUM_REGS_KEY 8

// Number registers for initialization vector
#define AES_PARAM_NUM_REGS_IV 4

// Number registers for input and output data
#define AES_PARAM_NUM_REGS_DATA 4

// Number of alerts
#define AES_PARAM_NUM_ALERTS 2

// Register width
#define AES_PARAM_REG_WIDTH 32

// Alert Test Register
#define AES_ALERT_TEST_REG_OFFSET 0x0
#define AES_ALERT_TEST_REG_RESVAL 0x0
#define AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT 0
#define AES_ALERT_TEST_FATAL_FAULT_BIT 1

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_KEY_SHARE0_FIELD_WIDTH 32
#define AES_KEY_SHARE0_MULTIREG_COUNT 8

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_0_REG_OFFSET 0x4
#define AES_KEY_SHARE0_0_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_1_REG_OFFSET 0x8
#define AES_KEY_SHARE0_1_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_2_REG_OFFSET 0xc
#define AES_KEY_SHARE0_2_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_3_REG_OFFSET 0x10
#define AES_KEY_SHARE0_3_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_4_REG_OFFSET 0x14
#define AES_KEY_SHARE0_4_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_5_REG_OFFSET 0x18
#define AES_KEY_SHARE0_5_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_6_REG_OFFSET 0x1c
#define AES_KEY_SHARE0_6_REG_RESVAL 0x0

// Initial Key Registers Share 0.
#define AES_KEY_SHARE0_7_REG_OFFSET 0x20
#define AES_KEY_SHARE0_7_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_KEY_SHARE1_FIELD_WIDTH 32
#define AES_KEY_SHARE1_MULTIREG_COUNT 8

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_0_REG_OFFSET 0x24
#define AES_KEY_SHARE1_0_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_1_REG_OFFSET 0x28
#define AES_KEY_SHARE1_1_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_2_REG_OFFSET 0x2c
#define AES_KEY_SHARE1_2_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_3_REG_OFFSET 0x30
#define AES_KEY_SHARE1_3_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_4_REG_OFFSET 0x34
#define AES_KEY_SHARE1_4_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_5_REG_OFFSET 0x38
#define AES_KEY_SHARE1_5_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_6_REG_OFFSET 0x3c
#define AES_KEY_SHARE1_6_REG_RESVAL 0x0

// Initial Key Registers Share 1.
#define AES_KEY_SHARE1_7_REG_OFFSET 0x40
#define AES_KEY_SHARE1_7_REG_RESVAL 0x0

// Initialization Vector Registers.
#define AES_IV_IV_FIELD_WIDTH 32
#define AES_IV_MULTIREG_COUNT 4

// Initialization Vector Registers.
#define AES_IV_0_REG_OFFSET 0x44
#define AES_IV_0_REG_RESVAL 0x0

// Initialization Vector Registers.
#define AES_IV_1_REG_OFFSET 0x48
#define AES_IV_1_REG_RESVAL 0x0

// Initialization Vector Registers.
#define AES_IV_2_REG_OFFSET 0x4c
#define AES_IV_2_REG_RESVAL 0x0

// Initialization Vector Registers.
#define AES_IV_3_REG_OFFSET 0x50
#define AES_IV_3_REG_RESVAL 0x0

// Input Data Registers.
#define AES_DATA_IN_DATA_IN_FIELD_WIDTH 32
#define AES_DATA_IN_MULTIREG_COUNT 4

// Input Data Registers.
#define AES_DATA_IN_0_REG_OFFSET 0x54
#define AES_DATA_IN_0_REG_RESVAL 0x0

// Input Data Registers.
#define AES_DATA_IN_1_REG_OFFSET 0x58
#define AES_DATA_IN_1_REG_RESVAL 0x0

// Input Data Registers.
#define AES_DATA_IN_2_REG_OFFSET 0x5c
#define AES_DATA_IN_2_REG_RESVAL 0x0

// Input Data Registers.
#define AES_DATA_IN_3_REG_OFFSET 0x60
#define AES_DATA_IN_3_REG_RESVAL 0x0

// Output Data Register.
#define AES_DATA_OUT_DATA_OUT_FIELD_WIDTH 32
#define AES_DATA_OUT_MULTIREG_COUNT 4

// Output Data Register.
#define AES_DATA_OUT_0_REG_OFFSET 0x64
#define AES_DATA_OUT_0_REG_RESVAL 0x0

// Output Data Register.
#define AES_DATA_OUT_1_REG_OFFSET 0x68
#define AES_DATA_OUT_1_REG_RESVAL 0x0

// Output Data Register.
#define AES_DATA_OUT_2_REG_OFFSET 0x6c
#define AES_DATA_OUT_2_REG_RESVAL 0x0

// Output Data Register.
#define AES_DATA_OUT_3_REG_OFFSET 0x70
#define AES_DATA_OUT_3_REG_RESVAL 0x0

// Control Register.
#define AES_CTRL_SHADOWED_REG_OFFSET 0x74
#define AES_CTRL_SHADOWED_REG_RESVAL 0x1181
#define AES_CTRL_SHADOWED_OPERATION_MASK 0x3
#define AES_CTRL_SHADOWED_OPERATION_OFFSET 0
#define AES_CTRL_SHADOWED_OPERATION_FIELD \
  ((bitfield_field32_t) { .mask = AES_CTRL_SHADOWED_OPERATION_MASK, .index = AES_CTRL_SHADOWED_OPERATION_OFFSET })
#define AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC 0x1
#define AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC 0x2
#define AES_CTRL_SHADOWED_MODE_MASK 0x3f
#define AES_CTRL_SHADOWED_MODE_OFFSET 2
#define AES_CTRL_SHADOWED_MODE_FIELD \
  ((bitfield_field32_t) { .mask = AES_CTRL_SHADOWED_MODE_MASK, .index = AES_CTRL_SHADOWED_MODE_OFFSET })
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB 0x1
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC 0x2
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB 0x4
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB 0x8
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR 0x10
#define AES_CTRL_SHADOWED_MODE_VALUE_AES_NONE 0x20
#define AES_CTRL_SHADOWED_KEY_LEN_MASK 0x7
#define AES_CTRL_SHADOWED_KEY_LEN_OFFSET 8
#define AES_CTRL_SHADOWED_KEY_LEN_FIELD \
  ((bitfield_field32_t) { .mask = AES_CTRL_SHADOWED_KEY_LEN_MASK, .index = AES_CTRL_SHADOWED_KEY_LEN_OFFSET })
#define AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128 0x1
#define AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192 0x2
#define AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256 0x4
#define AES_CTRL_SHADOWED_SIDELOAD_BIT 11
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_MASK 0x7
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_OFFSET 12
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_FIELD \
  ((bitfield_field32_t) { .mask = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_MASK, .index = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_OFFSET })
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1 0x1
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64 0x2
#define AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_8K 0x4
#define AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT 15

// Auxiliary Control Register.
#define AES_CTRL_AUX_SHADOWED_REG_OFFSET 0x78
#define AES_CTRL_AUX_SHADOWED_REG_RESVAL 0x1
#define AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT 0
#define AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT 1

// Lock bit for Auxiliary Control Register.
#define AES_CTRL_AUX_REGWEN_REG_OFFSET 0x7c
#define AES_CTRL_AUX_REGWEN_REG_RESVAL 0x1
#define AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT 0

// Trigger Register.
#define AES_TRIGGER_REG_OFFSET 0x80
#define AES_TRIGGER_REG_RESVAL 0xe
#define AES_TRIGGER_START_BIT 0
#define AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT 1
#define AES_TRIGGER_DATA_OUT_CLEAR_BIT 2
#define AES_TRIGGER_PRNG_RESEED_BIT 3

// Status Register
#define AES_STATUS_REG_OFFSET 0x84
#define AES_STATUS_REG_RESVAL 0x0
#define AES_STATUS_IDLE_BIT 0
#define AES_STATUS_STALL_BIT 1
#define AES_STATUS_OUTPUT_LOST_BIT 2
#define AES_STATUS_OUTPUT_VALID_BIT 3
#define AES_STATUS_INPUT_READY_BIT 4
#define AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT 5
#define AES_STATUS_ALERT_FATAL_FAULT_BIT 6

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _AES_REG_DEFS_
// End generated register defines for aes