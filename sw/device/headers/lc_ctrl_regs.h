// Generated register defines for lc_ctrl

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _LC_CTRL_REG_DEFS_
#define _LC_CTRL_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Width of hardware revision fields.
#define LC_CTRL_PARAM_HW_REV_FIELD_WIDTH 16

// Number of 32bit words in a token.
#define LC_CTRL_PARAM_NUM_TOKEN_WORDS 4

// Number of life cycle state enum bits.
#define LC_CTRL_PARAM_CSR_LC_STATE_WIDTH 30

// Number of life cycle transition counter bits.
#define LC_CTRL_PARAM_CSR_LC_COUNT_WIDTH 5

// Number of life cycle id state enum bits.
#define LC_CTRL_PARAM_CSR_LC_ID_STATE_WIDTH 32

// Number of vendor/test-specific OTP control bits.
#define LC_CTRL_PARAM_CSR_OTP_TEST_CTRL_WIDTH 32

// Number of vendor/test-specific OTP status bits.
#define LC_CTRL_PARAM_CSR_OTP_TEST_STATUS_WIDTH 32

// Number of 32bit words in the Device ID.
#define LC_CTRL_PARAM_NUM_DEVICE_ID_WORDS 8

// Number of 32bit words in the manufacturing state.
#define LC_CTRL_PARAM_NUM_MANUF_STATE_WORDS 8

// Number of alerts
#define LC_CTRL_PARAM_NUM_ALERTS 3

// Register width
#define LC_CTRL_PARAM_REG_WIDTH 32

// Alert Test Register
#define LC_CTRL_ALERT_TEST_REG_OFFSET 0x0
#define LC_CTRL_ALERT_TEST_REG_RESVAL 0x0
#define LC_CTRL_ALERT_TEST_FATAL_PROG_ERROR_BIT 0
#define LC_CTRL_ALERT_TEST_FATAL_STATE_ERROR_BIT 1
#define LC_CTRL_ALERT_TEST_FATAL_BUS_INTEG_ERROR_BIT 2

// life cycle status register. Note that all errors are terminal and require
// a reset cycle.
#define LC_CTRL_STATUS_REG_OFFSET 0x4
#define LC_CTRL_STATUS_REG_RESVAL 0x0
#define LC_CTRL_STATUS_INITIALIZED_BIT 0
#define LC_CTRL_STATUS_READY_BIT 1
#define LC_CTRL_STATUS_TRANSITION_SUCCESSFUL_BIT 2
#define LC_CTRL_STATUS_TRANSITION_COUNT_ERROR_BIT 3
#define LC_CTRL_STATUS_TRANSITION_ERROR_BIT 4
#define LC_CTRL_STATUS_TOKEN_ERROR_BIT 5
#define LC_CTRL_STATUS_FLASH_RMA_ERROR_BIT 6
#define LC_CTRL_STATUS_OTP_ERROR_BIT 7
#define LC_CTRL_STATUS_STATE_ERROR_BIT 8
#define LC_CTRL_STATUS_BUS_INTEG_ERROR_BIT 9
#define LC_CTRL_STATUS_OTP_PARTITION_ERROR_BIT 10

// Hardware mutex to claim exclusive access to the transition interface.
#define LC_CTRL_CLAIM_TRANSITION_IF_REG_OFFSET 0x8
#define LC_CTRL_CLAIM_TRANSITION_IF_REG_RESVAL 0x69
#define LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_MASK 0xff
#define LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_OFFSET 0
#define LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_MASK, .index = LC_CTRL_CLAIM_TRANSITION_IF_MUTEX_OFFSET })

// Register write enable for all transition interface registers.
#define LC_CTRL_TRANSITION_REGWEN_REG_OFFSET 0xc
#define LC_CTRL_TRANSITION_REGWEN_REG_RESVAL 0x0
#define LC_CTRL_TRANSITION_REGWEN_TRANSITION_REGWEN_BIT 0

// Command register for state transition requests.
#define LC_CTRL_TRANSITION_CMD_REG_OFFSET 0x10
#define LC_CTRL_TRANSITION_CMD_REG_RESVAL 0x0
#define LC_CTRL_TRANSITION_CMD_START_BIT 0

// Control register for state transition requests.
#define LC_CTRL_TRANSITION_CTRL_REG_OFFSET 0x14
#define LC_CTRL_TRANSITION_CTRL_REG_RESVAL 0x0
#define LC_CTRL_TRANSITION_CTRL_EXT_CLOCK_EN_BIT 0

// 128bit token for conditional transitions.
#define LC_CTRL_TRANSITION_TOKEN_TRANSITION_TOKEN_FIELD_WIDTH 32
#define LC_CTRL_TRANSITION_TOKEN_MULTIREG_COUNT 4

// 128bit token for conditional transitions.
#define LC_CTRL_TRANSITION_TOKEN_0_REG_OFFSET 0x18
#define LC_CTRL_TRANSITION_TOKEN_0_REG_RESVAL 0x0

// 128bit token for conditional transitions.
#define LC_CTRL_TRANSITION_TOKEN_1_REG_OFFSET 0x1c
#define LC_CTRL_TRANSITION_TOKEN_1_REG_RESVAL 0x0

// 128bit token for conditional transitions.
#define LC_CTRL_TRANSITION_TOKEN_2_REG_OFFSET 0x20
#define LC_CTRL_TRANSITION_TOKEN_2_REG_RESVAL 0x0

// 128bit token for conditional transitions.
#define LC_CTRL_TRANSITION_TOKEN_3_REG_OFFSET 0x24
#define LC_CTRL_TRANSITION_TOKEN_3_REG_RESVAL 0x0

// This register exposes the decoded life cycle state.
#define LC_CTRL_TRANSITION_TARGET_REG_OFFSET 0x28
#define LC_CTRL_TRANSITION_TARGET_REG_RESVAL 0x0
#define LC_CTRL_TRANSITION_TARGET_STATE_MASK 0x3fffffff
#define LC_CTRL_TRANSITION_TARGET_STATE_OFFSET 0
#define LC_CTRL_TRANSITION_TARGET_STATE_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_TRANSITION_TARGET_STATE_MASK, .index = LC_CTRL_TRANSITION_TARGET_STATE_OFFSET })
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_RAW 0x0
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED0 0x2108421
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED0 0x4210842
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED1 0x6318c63
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED1 0x8421084
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED2 0xa5294a5
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED2 0xc6318c6
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED3 0xe739ce7
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED3 0x10842108
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED4 0x1294a529
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED4 0x14a5294a
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED5 0x16b5ad6b
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED5 0x18c6318c
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED6 0x1ad6b5ad
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_LOCKED6 0x1ce739ce
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_TEST_UNLOCKED7 0x1ef7bdef
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_DEV 0x21084210
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD 0x2318c631
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_PROD_END 0x25294a52
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_RMA 0x2739ce73
#define LC_CTRL_TRANSITION_TARGET_STATE_VALUE_SCRAP 0x294a5294

// Test/vendor-specific settings for the OTP macro wrapper.
#define LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_OFFSET 0x2c
#define LC_CTRL_OTP_VENDOR_TEST_CTRL_REG_RESVAL 0x0

// Test/vendor-specific settings for the OTP macro wrapper.
#define LC_CTRL_OTP_VENDOR_TEST_STATUS_REG_OFFSET 0x30
#define LC_CTRL_OTP_VENDOR_TEST_STATUS_REG_RESVAL 0x0

// This register exposes the decoded life cycle state.
#define LC_CTRL_LC_STATE_REG_OFFSET 0x34
#define LC_CTRL_LC_STATE_REG_RESVAL 0x0
#define LC_CTRL_LC_STATE_STATE_MASK 0x3fffffff
#define LC_CTRL_LC_STATE_STATE_OFFSET 0
#define LC_CTRL_LC_STATE_STATE_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_LC_STATE_STATE_MASK, .index = LC_CTRL_LC_STATE_STATE_OFFSET })
#define LC_CTRL_LC_STATE_STATE_VALUE_RAW 0x0
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED0 0x2108421
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED0 0x4210842
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED1 0x6318c63
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED1 0x8421084
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED2 0xa5294a5
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED2 0xc6318c6
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED3 0xe739ce7
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED3 0x10842108
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED4 0x1294a529
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED4 0x14a5294a
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED5 0x16b5ad6b
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED5 0x18c6318c
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED6 0x1ad6b5ad
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_LOCKED6 0x1ce739ce
#define LC_CTRL_LC_STATE_STATE_VALUE_TEST_UNLOCKED7 0x1ef7bdef
#define LC_CTRL_LC_STATE_STATE_VALUE_DEV 0x21084210
#define LC_CTRL_LC_STATE_STATE_VALUE_PROD 0x2318c631
#define LC_CTRL_LC_STATE_STATE_VALUE_PROD_END 0x25294a52
#define LC_CTRL_LC_STATE_STATE_VALUE_RMA 0x2739ce73
#define LC_CTRL_LC_STATE_STATE_VALUE_SCRAP 0x294a5294
#define LC_CTRL_LC_STATE_STATE_VALUE_POST_TRANSITION 0x2b5ad6b5
#define LC_CTRL_LC_STATE_STATE_VALUE_ESCALATE 0x2d6b5ad6
#define LC_CTRL_LC_STATE_STATE_VALUE_INVALID 0x2f7bdef7

// This register exposes the state of the decoded life cycle transition
// counter.
#define LC_CTRL_LC_TRANSITION_CNT_REG_OFFSET 0x38
#define LC_CTRL_LC_TRANSITION_CNT_REG_RESVAL 0x0
#define LC_CTRL_LC_TRANSITION_CNT_CNT_MASK 0x1f
#define LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET 0
#define LC_CTRL_LC_TRANSITION_CNT_CNT_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_LC_TRANSITION_CNT_CNT_MASK, .index = LC_CTRL_LC_TRANSITION_CNT_CNT_OFFSET })

// This register exposes the id state of the device.
#define LC_CTRL_LC_ID_STATE_REG_OFFSET 0x3c
#define LC_CTRL_LC_ID_STATE_REG_RESVAL 0x0
#define LC_CTRL_LC_ID_STATE_STATE_VALUE_BLANK 0x0
#define LC_CTRL_LC_ID_STATE_STATE_VALUE_PERSONALIZED 0x11111111
#define LC_CTRL_LC_ID_STATE_STATE_VALUE_INVALID 0x22222222

// This register holds the 32bit hardware revision,
#define LC_CTRL_HW_REV_REG_OFFSET 0x40
#define LC_CTRL_HW_REV_REG_RESVAL 0x0
#define LC_CTRL_HW_REV_CHIP_REV_MASK 0xffff
#define LC_CTRL_HW_REV_CHIP_REV_OFFSET 0
#define LC_CTRL_HW_REV_CHIP_REV_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_HW_REV_CHIP_REV_MASK, .index = LC_CTRL_HW_REV_CHIP_REV_OFFSET })
#define LC_CTRL_HW_REV_CHIP_GEN_MASK 0xffff
#define LC_CTRL_HW_REV_CHIP_GEN_OFFSET 16
#define LC_CTRL_HW_REV_CHIP_GEN_FIELD \
  ((bitfield_field32_t) { .mask = LC_CTRL_HW_REV_CHIP_GEN_MASK, .index = LC_CTRL_HW_REV_CHIP_GEN_OFFSET })

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_DEVICE_ID_FIELD_WIDTH 32
#define LC_CTRL_DEVICE_ID_MULTIREG_COUNT 8

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_0_REG_OFFSET 0x44
#define LC_CTRL_DEVICE_ID_0_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_1_REG_OFFSET 0x48
#define LC_CTRL_DEVICE_ID_1_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_2_REG_OFFSET 0x4c
#define LC_CTRL_DEVICE_ID_2_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_3_REG_OFFSET 0x50
#define LC_CTRL_DEVICE_ID_3_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_4_REG_OFFSET 0x54
#define LC_CTRL_DEVICE_ID_4_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_5_REG_OFFSET 0x58
#define LC_CTRL_DEVICE_ID_5_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_6_REG_OFFSET 0x5c
#define LC_CTRL_DEVICE_ID_6_REG_RESVAL 0x0

// This is the 256bit DEVICE_ID value that is stored in the HW_CFG partition
// in OTP.
#define LC_CTRL_DEVICE_ID_7_REG_OFFSET 0x60
#define LC_CTRL_DEVICE_ID_7_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
// (common parameters)
#define LC_CTRL_MANUF_STATE_MANUF_STATE_FIELD_WIDTH 32
#define LC_CTRL_MANUF_STATE_MULTIREG_COUNT 8

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_0_REG_OFFSET 0x64
#define LC_CTRL_MANUF_STATE_0_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_1_REG_OFFSET 0x68
#define LC_CTRL_MANUF_STATE_1_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_2_REG_OFFSET 0x6c
#define LC_CTRL_MANUF_STATE_2_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_3_REG_OFFSET 0x70
#define LC_CTRL_MANUF_STATE_3_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_4_REG_OFFSET 0x74
#define LC_CTRL_MANUF_STATE_4_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_5_REG_OFFSET 0x78
#define LC_CTRL_MANUF_STATE_5_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_6_REG_OFFSET 0x7c
#define LC_CTRL_MANUF_STATE_6_REG_RESVAL 0x0

// This is a 256bit field used for keeping track of the manufacturing state.
#define LC_CTRL_MANUF_STATE_7_REG_OFFSET 0x80
#define LC_CTRL_MANUF_STATE_7_REG_RESVAL 0x0

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _LC_CTRL_REG_DEFS_
// End generated register defines for lc_ctrl