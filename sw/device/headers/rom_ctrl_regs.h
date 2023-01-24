// Generated register defines for rom_ctrl

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _ROM_CTRL_REG_DEFS_
#define _ROM_CTRL_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of alerts
#define ROM_CTRL_PARAM_NUM_ALERTS 1

// Register width
#define ROM_CTRL_PARAM_REG_WIDTH 32

// Alert Test Register
#define ROM_CTRL_ALERT_TEST_REG_OFFSET 0x0
#define ROM_CTRL_ALERT_TEST_REG_RESVAL 0x0
#define ROM_CTRL_ALERT_TEST_FATAL_BIT 0

// The cause of a fatal alert.
#define ROM_CTRL_FATAL_ALERT_CAUSE_REG_OFFSET 0x4
#define ROM_CTRL_FATAL_ALERT_CAUSE_REG_RESVAL 0x0
#define ROM_CTRL_FATAL_ALERT_CAUSE_CHECKER_ERROR_BIT 0
#define ROM_CTRL_FATAL_ALERT_CAUSE_INTEGRITY_ERROR_BIT 1

// The digest computed from the contents of ROM (common parameters)
#define ROM_CTRL_DIGEST_DIGEST_FIELD_WIDTH 32
#define ROM_CTRL_DIGEST_MULTIREG_COUNT 8

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_0_REG_OFFSET 0x8
#define ROM_CTRL_DIGEST_0_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_1_REG_OFFSET 0xc
#define ROM_CTRL_DIGEST_1_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_2_REG_OFFSET 0x10
#define ROM_CTRL_DIGEST_2_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_3_REG_OFFSET 0x14
#define ROM_CTRL_DIGEST_3_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_4_REG_OFFSET 0x18
#define ROM_CTRL_DIGEST_4_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_5_REG_OFFSET 0x1c
#define ROM_CTRL_DIGEST_5_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_6_REG_OFFSET 0x20
#define ROM_CTRL_DIGEST_6_REG_RESVAL 0x0

// The digest computed from the contents of ROM
#define ROM_CTRL_DIGEST_7_REG_OFFSET 0x24
#define ROM_CTRL_DIGEST_7_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM (common parameters)
#define ROM_CTRL_EXP_DIGEST_DIGEST_FIELD_WIDTH 32
#define ROM_CTRL_EXP_DIGEST_MULTIREG_COUNT 8

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_0_REG_OFFSET 0x28
#define ROM_CTRL_EXP_DIGEST_0_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_1_REG_OFFSET 0x2c
#define ROM_CTRL_EXP_DIGEST_1_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_2_REG_OFFSET 0x30
#define ROM_CTRL_EXP_DIGEST_2_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_3_REG_OFFSET 0x34
#define ROM_CTRL_EXP_DIGEST_3_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_4_REG_OFFSET 0x38
#define ROM_CTRL_EXP_DIGEST_4_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_5_REG_OFFSET 0x3c
#define ROM_CTRL_EXP_DIGEST_5_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_6_REG_OFFSET 0x40
#define ROM_CTRL_EXP_DIGEST_6_REG_RESVAL 0x0

// The expected digest, stored in the top words of ROM
#define ROM_CTRL_EXP_DIGEST_7_REG_OFFSET 0x44
#define ROM_CTRL_EXP_DIGEST_7_REG_RESVAL 0x0

// Memory area: ROM data
#define ROM_CTRL_ROM_REG_OFFSET 0x0
#define ROM_CTRL_ROM_SIZE_WORDS 8192
#define ROM_CTRL_ROM_SIZE_BYTES 32768
#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _ROM_CTRL_REG_DEFS_
// End generated register defines for rom_ctrl