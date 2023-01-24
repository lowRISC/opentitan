// Generated register defines for KEYMGR

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _KEYMGR_REG_DEFS_
#define _KEYMGR_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of Registers for SW inputs (Salt)
#define KEYMGR_PARAM_NUM_SALT_REG 8

// Number of Registers for SW inputs (SW binding)
#define KEYMGR_PARAM_NUM_SW_BINDING_REG 8

// Number of Registers for SW outputs
#define KEYMGR_PARAM_NUM_OUT_REG 8

// Number of Registers for key version
#define KEYMGR_PARAM_NUM_KEY_VERSION 1

// Number of alerts
#define KEYMGR_PARAM_NUM_ALERTS 2

// Register width
#define KEYMGR_PARAM_REG_WIDTH 32

// Common Interrupt Offsets
#define KEYMGR_INTR_COMMON_OP_DONE_BIT 0

// Interrupt State Register
#define KEYMGR_INTR_STATE_REG_OFFSET 0x0
#define KEYMGR_INTR_STATE_REG_RESVAL 0x0
#define KEYMGR_INTR_STATE_OP_DONE_BIT 0

// Interrupt Enable Register
#define KEYMGR_INTR_ENABLE_REG_OFFSET 0x4
#define KEYMGR_INTR_ENABLE_REG_RESVAL 0x0
#define KEYMGR_INTR_ENABLE_OP_DONE_BIT 0

// Interrupt Test Register
#define KEYMGR_INTR_TEST_REG_OFFSET 0x8
#define KEYMGR_INTR_TEST_REG_RESVAL 0x0
#define KEYMGR_INTR_TEST_OP_DONE_BIT 0

// Alert Test Register
#define KEYMGR_ALERT_TEST_REG_OFFSET 0xc
#define KEYMGR_ALERT_TEST_REG_RESVAL 0x0
#define KEYMGR_ALERT_TEST_RECOV_OPERATION_ERR_BIT 0
#define KEYMGR_ALERT_TEST_FATAL_FAULT_ERR_BIT 1

// Key manager configuration enable
#define KEYMGR_CFG_REGWEN_REG_OFFSET 0x10
#define KEYMGR_CFG_REGWEN_REG_RESVAL 0x1
#define KEYMGR_CFG_REGWEN_EN_BIT 0

// Key manager operation start
#define KEYMGR_START_REG_OFFSET 0x14
#define KEYMGR_START_REG_RESVAL 0x0
#define KEYMGR_START_EN_BIT 0

// Key manager operation controls
#define KEYMGR_CONTROL_SHADOWED_REG_OFFSET 0x18
#define KEYMGR_CONTROL_SHADOWED_REG_RESVAL 0x10
#define KEYMGR_CONTROL_SHADOWED_OPERATION_MASK 0x7
#define KEYMGR_CONTROL_SHADOWED_OPERATION_OFFSET 4
#define KEYMGR_CONTROL_SHADOWED_OPERATION_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_CONTROL_SHADOWED_OPERATION_MASK, .index = KEYMGR_CONTROL_SHADOWED_OPERATION_OFFSET })
#define KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE 0x0
#define KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_ID 0x1
#define KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_SW_OUTPUT 0x2
#define KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT 0x3
#define KEYMGR_CONTROL_SHADOWED_OPERATION_VALUE_DISABLE 0x4
#define KEYMGR_CONTROL_SHADOWED_CDI_SEL_BIT 7
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_MASK 0x3
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_OFFSET 12
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_CONTROL_SHADOWED_DEST_SEL_MASK, .index = KEYMGR_CONTROL_SHADOWED_DEST_SEL_OFFSET })
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE 0x0
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_AES 0x1
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_KMAC 0x2
#define KEYMGR_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN 0x3

// sideload key slots clear
#define KEYMGR_SIDELOAD_CLEAR_REG_OFFSET 0x1c
#define KEYMGR_SIDELOAD_CLEAR_REG_RESVAL 0x0
#define KEYMGR_SIDELOAD_CLEAR_VAL_MASK 0x7
#define KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET 0
#define KEYMGR_SIDELOAD_CLEAR_VAL_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_SIDELOAD_CLEAR_VAL_MASK, .index = KEYMGR_SIDELOAD_CLEAR_VAL_OFFSET })
#define KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_NONE 0x0
#define KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_AES 0x1
#define KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_KMAC 0x2
#define KEYMGR_SIDELOAD_CLEAR_VAL_VALUE_OTBN 0x3

// regwen for reseed interval
#define KEYMGR_RESEED_INTERVAL_REGWEN_REG_OFFSET 0x20
#define KEYMGR_RESEED_INTERVAL_REGWEN_REG_RESVAL 0x1
#define KEYMGR_RESEED_INTERVAL_REGWEN_EN_BIT 0

// Reseed interval for key manager entropy reseed
#define KEYMGR_RESEED_INTERVAL_SHADOWED_REG_OFFSET 0x24
#define KEYMGR_RESEED_INTERVAL_SHADOWED_REG_RESVAL 0x100
#define KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_MASK 0xffff
#define KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_OFFSET 0
#define KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_MASK, .index = KEYMGR_RESEED_INTERVAL_SHADOWED_VAL_OFFSET })

// Register write enable for SOFTWARE_BINDING
#define KEYMGR_SW_BINDING_REGWEN_REG_OFFSET 0x28
#define KEYMGR_SW_BINDING_REGWEN_REG_RESVAL 0x1
#define KEYMGR_SW_BINDING_REGWEN_EN_BIT 0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_VAL_FIELD_WIDTH 32
#define KEYMGR_SEALING_SW_BINDING_MULTIREG_COUNT 8

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_0_REG_OFFSET 0x2c
#define KEYMGR_SEALING_SW_BINDING_0_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_1_REG_OFFSET 0x30
#define KEYMGR_SEALING_SW_BINDING_1_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_2_REG_OFFSET 0x34
#define KEYMGR_SEALING_SW_BINDING_2_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_3_REG_OFFSET 0x38
#define KEYMGR_SEALING_SW_BINDING_3_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_4_REG_OFFSET 0x3c
#define KEYMGR_SEALING_SW_BINDING_4_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_5_REG_OFFSET 0x40
#define KEYMGR_SEALING_SW_BINDING_5_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_6_REG_OFFSET 0x44
#define KEYMGR_SEALING_SW_BINDING_6_REG_RESVAL 0x0

// Software binding input to sealing portion of the key manager.
#define KEYMGR_SEALING_SW_BINDING_7_REG_OFFSET 0x48
#define KEYMGR_SEALING_SW_BINDING_7_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_VAL_FIELD_WIDTH 32
#define KEYMGR_ATTEST_SW_BINDING_MULTIREG_COUNT 8

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_0_REG_OFFSET 0x4c
#define KEYMGR_ATTEST_SW_BINDING_0_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_1_REG_OFFSET 0x50
#define KEYMGR_ATTEST_SW_BINDING_1_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_2_REG_OFFSET 0x54
#define KEYMGR_ATTEST_SW_BINDING_2_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_3_REG_OFFSET 0x58
#define KEYMGR_ATTEST_SW_BINDING_3_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_4_REG_OFFSET 0x5c
#define KEYMGR_ATTEST_SW_BINDING_4_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_5_REG_OFFSET 0x60
#define KEYMGR_ATTEST_SW_BINDING_5_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_6_REG_OFFSET 0x64
#define KEYMGR_ATTEST_SW_BINDING_6_REG_RESVAL 0x0

// Software binding input to the attestation portion of the key manager.
#define KEYMGR_ATTEST_SW_BINDING_7_REG_OFFSET 0x68
#define KEYMGR_ATTEST_SW_BINDING_7_REG_RESVAL 0x0

// Salt value used as part of output generation (common parameters)
#define KEYMGR_SALT_VAL_FIELD_WIDTH 32
#define KEYMGR_SALT_MULTIREG_COUNT 8

// Salt value used as part of output generation
#define KEYMGR_SALT_0_REG_OFFSET 0x6c
#define KEYMGR_SALT_0_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_1_REG_OFFSET 0x70
#define KEYMGR_SALT_1_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_2_REG_OFFSET 0x74
#define KEYMGR_SALT_2_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_3_REG_OFFSET 0x78
#define KEYMGR_SALT_3_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_4_REG_OFFSET 0x7c
#define KEYMGR_SALT_4_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_5_REG_OFFSET 0x80
#define KEYMGR_SALT_5_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_6_REG_OFFSET 0x84
#define KEYMGR_SALT_6_REG_RESVAL 0x0

// Salt value used as part of output generation
#define KEYMGR_SALT_7_REG_OFFSET 0x88
#define KEYMGR_SALT_7_REG_RESVAL 0x0

// Version used as part of output generation (common parameters)
#define KEYMGR_KEY_VERSION_VAL_FIELD_WIDTH 32
#define KEYMGR_KEY_VERSION_MULTIREG_COUNT 1

// Version used as part of output generation
#define KEYMGR_KEY_VERSION_REG_OFFSET 0x8c
#define KEYMGR_KEY_VERSION_REG_RESVAL 0x0

// Register write enable for MAX_CREATOR_KEY_VERSION
#define KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_OFFSET 0x90
#define KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_REG_RESVAL 0x1
#define KEYMGR_MAX_CREATOR_KEY_VER_REGWEN_EN_BIT 0

// Max creator key version
#define KEYMGR_MAX_CREATOR_KEY_VER_SHADOWED_REG_OFFSET 0x94
#define KEYMGR_MAX_CREATOR_KEY_VER_SHADOWED_REG_RESVAL 0x0

// Register write enable for MAX_OWNER_INT_KEY_VERSION
#define KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_OFFSET 0x98
#define KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_REG_RESVAL 0x1
#define KEYMGR_MAX_OWNER_INT_KEY_VER_REGWEN_EN_BIT 0

// Max owner intermediate key version
#define KEYMGR_MAX_OWNER_INT_KEY_VER_SHADOWED_REG_OFFSET 0x9c
#define KEYMGR_MAX_OWNER_INT_KEY_VER_SHADOWED_REG_RESVAL 0x1

// Register write enable for MAX_OWNER_KEY_VERSION
#define KEYMGR_MAX_OWNER_KEY_VER_REGWEN_REG_OFFSET 0xa0
#define KEYMGR_MAX_OWNER_KEY_VER_REGWEN_REG_RESVAL 0x1
#define KEYMGR_MAX_OWNER_KEY_VER_REGWEN_EN_BIT 0

// Max owner key version
#define KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_OFFSET 0xa4
#define KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_VAL_FIELD_WIDTH 32
#define KEYMGR_SW_SHARE0_OUTPUT_MULTIREG_COUNT 8

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_0_REG_OFFSET 0xa8
#define KEYMGR_SW_SHARE0_OUTPUT_0_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_1_REG_OFFSET 0xac
#define KEYMGR_SW_SHARE0_OUTPUT_1_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_2_REG_OFFSET 0xb0
#define KEYMGR_SW_SHARE0_OUTPUT_2_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_3_REG_OFFSET 0xb4
#define KEYMGR_SW_SHARE0_OUTPUT_3_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_4_REG_OFFSET 0xb8
#define KEYMGR_SW_SHARE0_OUTPUT_4_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_5_REG_OFFSET 0xbc
#define KEYMGR_SW_SHARE0_OUTPUT_5_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_6_REG_OFFSET 0xc0
#define KEYMGR_SW_SHARE0_OUTPUT_6_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE0_OUTPUT_7_REG_OFFSET 0xc4
#define KEYMGR_SW_SHARE0_OUTPUT_7_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_VAL_FIELD_WIDTH 32
#define KEYMGR_SW_SHARE1_OUTPUT_MULTIREG_COUNT 8

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_0_REG_OFFSET 0xc8
#define KEYMGR_SW_SHARE1_OUTPUT_0_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_1_REG_OFFSET 0xcc
#define KEYMGR_SW_SHARE1_OUTPUT_1_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_2_REG_OFFSET 0xd0
#define KEYMGR_SW_SHARE1_OUTPUT_2_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_3_REG_OFFSET 0xd4
#define KEYMGR_SW_SHARE1_OUTPUT_3_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_4_REG_OFFSET 0xd8
#define KEYMGR_SW_SHARE1_OUTPUT_4_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_5_REG_OFFSET 0xdc
#define KEYMGR_SW_SHARE1_OUTPUT_5_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_6_REG_OFFSET 0xe0
#define KEYMGR_SW_SHARE1_OUTPUT_6_REG_RESVAL 0x0

// Key manager software output.
#define KEYMGR_SW_SHARE1_OUTPUT_7_REG_OFFSET 0xe4
#define KEYMGR_SW_SHARE1_OUTPUT_7_REG_RESVAL 0x0

// Key manager working state.
#define KEYMGR_WORKING_STATE_REG_OFFSET 0xe8
#define KEYMGR_WORKING_STATE_REG_RESVAL 0x0
#define KEYMGR_WORKING_STATE_STATE_MASK 0x7
#define KEYMGR_WORKING_STATE_STATE_OFFSET 0
#define KEYMGR_WORKING_STATE_STATE_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_WORKING_STATE_STATE_MASK, .index = KEYMGR_WORKING_STATE_STATE_OFFSET })
#define KEYMGR_WORKING_STATE_STATE_VALUE_RESET 0x0
#define KEYMGR_WORKING_STATE_STATE_VALUE_INIT 0x1
#define KEYMGR_WORKING_STATE_STATE_VALUE_CREATOR_ROOT_KEY 0x2
#define KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_INTERMEDIATE_KEY 0x3
#define KEYMGR_WORKING_STATE_STATE_VALUE_OWNER_KEY 0x4
#define KEYMGR_WORKING_STATE_STATE_VALUE_DISABLED 0x5
#define KEYMGR_WORKING_STATE_STATE_VALUE_INVALID 0x6

// Key manager status.
#define KEYMGR_OP_STATUS_REG_OFFSET 0xec
#define KEYMGR_OP_STATUS_REG_RESVAL 0x0
#define KEYMGR_OP_STATUS_STATUS_MASK 0x3
#define KEYMGR_OP_STATUS_STATUS_OFFSET 0
#define KEYMGR_OP_STATUS_STATUS_FIELD \
  ((bitfield_field32_t) { .mask = KEYMGR_OP_STATUS_STATUS_MASK, .index = KEYMGR_OP_STATUS_STATUS_OFFSET })
#define KEYMGR_OP_STATUS_STATUS_VALUE_IDLE 0x0
#define KEYMGR_OP_STATUS_STATUS_VALUE_WIP 0x1
#define KEYMGR_OP_STATUS_STATUS_VALUE_DONE_SUCCESS 0x2
#define KEYMGR_OP_STATUS_STATUS_VALUE_DONE_ERROR 0x3

// Key manager error code.
#define KEYMGR_ERR_CODE_REG_OFFSET 0xf0
#define KEYMGR_ERR_CODE_REG_RESVAL 0x0
#define KEYMGR_ERR_CODE_INVALID_OP_BIT 0
#define KEYMGR_ERR_CODE_INVALID_KMAC_INPUT_BIT 1
#define KEYMGR_ERR_CODE_INVALID_SHADOW_UPDATE_BIT 2

// This register represents both synchronous and asynchronous fatal faults.
#define KEYMGR_FAULT_STATUS_REG_OFFSET 0xf4
#define KEYMGR_FAULT_STATUS_REG_RESVAL 0x0
#define KEYMGR_FAULT_STATUS_CMD_BIT 0
#define KEYMGR_FAULT_STATUS_KMAC_FSM_BIT 1
#define KEYMGR_FAULT_STATUS_KMAC_DONE_BIT 2
#define KEYMGR_FAULT_STATUS_KMAC_OP_BIT 3
#define KEYMGR_FAULT_STATUS_KMAC_OUT_BIT 4
#define KEYMGR_FAULT_STATUS_REGFILE_INTG_BIT 5
#define KEYMGR_FAULT_STATUS_SHADOW_BIT 6
#define KEYMGR_FAULT_STATUS_CTRL_FSM_INTG_BIT 7
#define KEYMGR_FAULT_STATUS_CTRL_FSM_CHK_BIT 8
#define KEYMGR_FAULT_STATUS_CTRL_FSM_CNT_BIT 9
#define KEYMGR_FAULT_STATUS_RESEED_CNT_BIT 10
#define KEYMGR_FAULT_STATUS_SIDE_CTRL_FSM_BIT 11
#define KEYMGR_FAULT_STATUS_SIDE_CTRL_SEL_BIT 12
#define KEYMGR_FAULT_STATUS_KEY_ECC_BIT 13

// The register holds some debug information that may be convenient if keymgr
#define KEYMGR_DEBUG_REG_OFFSET 0xf8
#define KEYMGR_DEBUG_REG_RESVAL 0x0
#define KEYMGR_DEBUG_INVALID_CREATOR_SEED_BIT 0
#define KEYMGR_DEBUG_INVALID_OWNER_SEED_BIT 1
#define KEYMGR_DEBUG_INVALID_DEV_ID_BIT 2
#define KEYMGR_DEBUG_INVALID_HEALTH_STATE_BIT 3
#define KEYMGR_DEBUG_INVALID_KEY_VERSION_BIT 4
#define KEYMGR_DEBUG_INVALID_KEY_BIT 5
#define KEYMGR_DEBUG_INVALID_DIGEST_BIT 6

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _KEYMGR_REG_DEFS_
// End generated register defines for KEYMGR