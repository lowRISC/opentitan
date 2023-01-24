// Generated register defines for hmac

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _HMAC_REG_DEFS_
#define _HMAC_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of words for digest/ key
#define HMAC_PARAM_NUM_WORDS 8

// Number of alerts
#define HMAC_PARAM_NUM_ALERTS 1

// Register width
#define HMAC_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define HMAC_INTR_COMMON_HMAC_DONE_BIT 0
#define HMAC_INTR_COMMON_FIFO_EMPTY_BIT 1
#define HMAC_INTR_COMMON_HMAC_ERR_BIT 2

// Interrupt State Register
#define HMAC_INTR_STATE_REG_OFFSET 0x0
#define HMAC_INTR_STATE_REG_RESVAL 0x0
#define HMAC_INTR_STATE_HMAC_DONE_BIT 0
#define HMAC_INTR_STATE_FIFO_EMPTY_BIT 1
#define HMAC_INTR_STATE_HMAC_ERR_BIT 2

// Interrupt Enable Register
#define HMAC_INTR_ENABLE_REG_OFFSET 0x4
#define HMAC_INTR_ENABLE_REG_RESVAL 0x0
#define HMAC_INTR_ENABLE_HMAC_DONE_BIT 0
#define HMAC_INTR_ENABLE_FIFO_EMPTY_BIT 1
#define HMAC_INTR_ENABLE_HMAC_ERR_BIT 2

// Interrupt Test Register
#define HMAC_INTR_TEST_REG_OFFSET 0x8
#define HMAC_INTR_TEST_REG_RESVAL 0x0
#define HMAC_INTR_TEST_HMAC_DONE_BIT 0
#define HMAC_INTR_TEST_FIFO_EMPTY_BIT 1
#define HMAC_INTR_TEST_HMAC_ERR_BIT 2

// Alert Test Register
#define HMAC_ALERT_TEST_REG_OFFSET 0xc
#define HMAC_ALERT_TEST_REG_RESVAL 0x0
#define HMAC_ALERT_TEST_FATAL_FAULT_BIT 0

// HMAC Configuration register.
#define HMAC_CFG_REG_OFFSET 0x10
#define HMAC_CFG_REG_RESVAL 0x0
#define HMAC_CFG_HMAC_EN_BIT 0
#define HMAC_CFG_SHA_EN_BIT 1
#define HMAC_CFG_ENDIAN_SWAP_BIT 2
#define HMAC_CFG_DIGEST_SWAP_BIT 3

// HMAC command register
#define HMAC_CMD_REG_OFFSET 0x14
#define HMAC_CMD_REG_RESVAL 0x0
#define HMAC_CMD_HASH_START_BIT 0
#define HMAC_CMD_HASH_PROCESS_BIT 1

// HMAC Status register
#define HMAC_STATUS_REG_OFFSET 0x18
#define HMAC_STATUS_REG_RESVAL 0x1
#define HMAC_STATUS_FIFO_EMPTY_BIT 0
#define HMAC_STATUS_FIFO_FULL_BIT 1
#define HMAC_STATUS_FIFO_DEPTH_MASK 0x1f
#define HMAC_STATUS_FIFO_DEPTH_OFFSET 4
#define HMAC_STATUS_FIFO_DEPTH_FIELD \
  ((bitfield_field32_t) { .mask = HMAC_STATUS_FIFO_DEPTH_MASK, .index = HMAC_STATUS_FIFO_DEPTH_OFFSET })

// HMAC Error Code
#define HMAC_ERR_CODE_REG_OFFSET 0x1c
#define HMAC_ERR_CODE_REG_RESVAL 0x0

// Randomize internal secret registers.
#define HMAC_WIPE_SECRET_REG_OFFSET 0x20
#define HMAC_WIPE_SECRET_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_KEY_FIELD_WIDTH 32
#define HMAC_KEY_MULTIREG_COUNT 8

// HMAC Secret Key
#define HMAC_KEY_0_REG_OFFSET 0x24
#define HMAC_KEY_0_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_1_REG_OFFSET 0x28
#define HMAC_KEY_1_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_2_REG_OFFSET 0x2c
#define HMAC_KEY_2_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_3_REG_OFFSET 0x30
#define HMAC_KEY_3_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_4_REG_OFFSET 0x34
#define HMAC_KEY_4_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_5_REG_OFFSET 0x38
#define HMAC_KEY_5_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_6_REG_OFFSET 0x3c
#define HMAC_KEY_6_REG_RESVAL 0x0

// HMAC Secret Key
#define HMAC_KEY_7_REG_OFFSET 0x40
#define HMAC_KEY_7_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_DIGEST_FIELD_WIDTH 32
#define HMAC_DIGEST_MULTIREG_COUNT 8

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_0_REG_OFFSET 0x44
#define HMAC_DIGEST_0_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_1_REG_OFFSET 0x48
#define HMAC_DIGEST_1_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_2_REG_OFFSET 0x4c
#define HMAC_DIGEST_2_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_3_REG_OFFSET 0x50
#define HMAC_DIGEST_3_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_4_REG_OFFSET 0x54
#define HMAC_DIGEST_4_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_5_REG_OFFSET 0x58
#define HMAC_DIGEST_5_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_6_REG_OFFSET 0x5c
#define HMAC_DIGEST_6_REG_RESVAL 0x0

// Digest output. If HMAC is disabled, the register shows result of SHA256
#define HMAC_DIGEST_7_REG_OFFSET 0x60
#define HMAC_DIGEST_7_REG_RESVAL 0x0

// Received Message Length calculated by the HMAC in bits [31:0]
#define HMAC_MSG_LENGTH_LOWER_REG_OFFSET 0x64
#define HMAC_MSG_LENGTH_LOWER_REG_RESVAL 0x0

// Received Message Length calculated by the HMAC in bits [63:32]
#define HMAC_MSG_LENGTH_UPPER_REG_OFFSET 0x68
#define HMAC_MSG_LENGTH_UPPER_REG_RESVAL 0x0

// Memory area: Message FIFO. Any write to this window will be appended to
// the FIFO. Only the lower [1:0] bits of the address matter to writes within
// the window (for correctly dealing with non 32-bit writes)
#define HMAC_MSG_FIFO_REG_OFFSET 0x800
#define HMAC_MSG_FIFO_SIZE_WORDS 512
#define HMAC_MSG_FIFO_SIZE_BYTES 2048
#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _HMAC_REG_DEFS_
// End generated register defines for hmac