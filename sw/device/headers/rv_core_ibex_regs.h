// Generated register defines for RV_CORE_IBEX

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _RV_CORE_IBEX_REG_DEFS_
#define _RV_CORE_IBEX_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of software triggerable alerts
#define RV_CORE_IBEX_PARAM_NUM_SW_ALERTS 2

// Number of translatable regions per ibex bus
#define RV_CORE_IBEX_PARAM_NUM_REGIONS 2

// Number of scratch words maintained.
#define RV_CORE_IBEX_PARAM_NUM_SCRATCH_WORDS 8

// Number of alerts
#define RV_CORE_IBEX_PARAM_NUM_ALERTS 4

// Register width
#define RV_CORE_IBEX_PARAM_REG_WIDTH 32

// Alert Test Register
#define RV_CORE_IBEX_ALERT_TEST_REG_OFFSET 0x0
#define RV_CORE_IBEX_ALERT_TEST_REG_RESVAL 0x0
#define RV_CORE_IBEX_ALERT_TEST_FATAL_SW_ERR_BIT 0
#define RV_CORE_IBEX_ALERT_TEST_RECOV_SW_ERR_BIT 1
#define RV_CORE_IBEX_ALERT_TEST_FATAL_HW_ERR_BIT 2
#define RV_CORE_IBEX_ALERT_TEST_RECOV_HW_ERR_BIT 3

// Software recoverable error
#define RV_CORE_IBEX_SW_RECOV_ERR_REG_OFFSET 0x4
#define RV_CORE_IBEX_SW_RECOV_ERR_REG_RESVAL 0x9
#define RV_CORE_IBEX_SW_RECOV_ERR_VAL_MASK 0xf
#define RV_CORE_IBEX_SW_RECOV_ERR_VAL_OFFSET 0
#define RV_CORE_IBEX_SW_RECOV_ERR_VAL_FIELD \
  ((bitfield_field32_t) { .mask = RV_CORE_IBEX_SW_RECOV_ERR_VAL_MASK, .index = RV_CORE_IBEX_SW_RECOV_ERR_VAL_OFFSET })

// Software fatal error
#define RV_CORE_IBEX_SW_FATAL_ERR_REG_OFFSET 0x8
#define RV_CORE_IBEX_SW_FATAL_ERR_REG_RESVAL 0x9
#define RV_CORE_IBEX_SW_FATAL_ERR_VAL_MASK 0xf
#define RV_CORE_IBEX_SW_FATAL_ERR_VAL_OFFSET 0
#define RV_CORE_IBEX_SW_FATAL_ERR_VAL_FIELD \
  ((bitfield_field32_t) { .mask = RV_CORE_IBEX_SW_FATAL_ERR_VAL_MASK, .index = RV_CORE_IBEX_SW_FATAL_ERR_VAL_OFFSET })

// Ibus address control regwen. (common parameters)
#define RV_CORE_IBEX_IBUS_REGWEN_EN_FIELD_WIDTH 1
#define RV_CORE_IBEX_IBUS_REGWEN_MULTIREG_COUNT 2

// Ibus address control regwen.
#define RV_CORE_IBEX_IBUS_REGWEN_0_REG_OFFSET 0xc
#define RV_CORE_IBEX_IBUS_REGWEN_0_REG_RESVAL 0x1
#define RV_CORE_IBEX_IBUS_REGWEN_0_EN_0_BIT 0

// Ibus address control regwen.
#define RV_CORE_IBEX_IBUS_REGWEN_1_REG_OFFSET 0x10
#define RV_CORE_IBEX_IBUS_REGWEN_1_REG_RESVAL 0x1
#define RV_CORE_IBEX_IBUS_REGWEN_1_EN_1_BIT 0

//   Enable Ibus address matching
#define RV_CORE_IBEX_IBUS_ADDR_EN_EN_FIELD_WIDTH 1
#define RV_CORE_IBEX_IBUS_ADDR_EN_MULTIREG_COUNT 2

//   Enable Ibus address matching
#define RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET 0x14
#define RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_RESVAL 0x0
#define RV_CORE_IBEX_IBUS_ADDR_EN_0_EN_0_BIT 0

//   Enable Ibus address matching
#define RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_OFFSET 0x18
#define RV_CORE_IBEX_IBUS_ADDR_EN_1_REG_RESVAL 0x0
#define RV_CORE_IBEX_IBUS_ADDR_EN_1_EN_1_BIT 0

//   Matching region programming for ibus.
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_VAL_FIELD_WIDTH 32
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_MULTIREG_COUNT 2

//   Matching region programming for ibus.
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET 0x1c
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_RESVAL 0x0

//   Matching region programming for ibus.
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_OFFSET 0x20
#define RV_CORE_IBEX_IBUS_ADDR_MATCHING_1_REG_RESVAL 0x0

//   The remap address after a match has been made.
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_VAL_FIELD_WIDTH 32
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_MULTIREG_COUNT 2

//   The remap address after a match has been made.
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET 0x24
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_RESVAL 0x0

//   The remap address after a match has been made.
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_OFFSET 0x28
#define RV_CORE_IBEX_IBUS_REMAP_ADDR_1_REG_RESVAL 0x0

// Dbus address control regwen. (common parameters)
#define RV_CORE_IBEX_DBUS_REGWEN_EN_FIELD_WIDTH 1
#define RV_CORE_IBEX_DBUS_REGWEN_MULTIREG_COUNT 2

// Dbus address control regwen.
#define RV_CORE_IBEX_DBUS_REGWEN_0_REG_OFFSET 0x2c
#define RV_CORE_IBEX_DBUS_REGWEN_0_REG_RESVAL 0x1
#define RV_CORE_IBEX_DBUS_REGWEN_0_EN_0_BIT 0

// Dbus address control regwen.
#define RV_CORE_IBEX_DBUS_REGWEN_1_REG_OFFSET 0x30
#define RV_CORE_IBEX_DBUS_REGWEN_1_REG_RESVAL 0x1
#define RV_CORE_IBEX_DBUS_REGWEN_1_EN_1_BIT 0

//   Enable dbus address matching
#define RV_CORE_IBEX_DBUS_ADDR_EN_EN_FIELD_WIDTH 1
#define RV_CORE_IBEX_DBUS_ADDR_EN_MULTIREG_COUNT 2

//   Enable dbus address matching
#define RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET 0x34
#define RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_RESVAL 0x0
#define RV_CORE_IBEX_DBUS_ADDR_EN_0_EN_0_BIT 0

//   Enable dbus address matching
#define RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_OFFSET 0x38
#define RV_CORE_IBEX_DBUS_ADDR_EN_1_REG_RESVAL 0x0
#define RV_CORE_IBEX_DBUS_ADDR_EN_1_EN_1_BIT 0

//   See !!IBUS_ADDR_MATCHING_0 for detailed description.
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_VAL_FIELD_WIDTH 32
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_MULTIREG_COUNT 2

//   See !!IBUS_ADDR_MATCHING_0 for detailed description.
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET 0x3c
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_RESVAL 0x0

//   See !!IBUS_ADDR_MATCHING_0 for detailed description.
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_OFFSET 0x40
#define RV_CORE_IBEX_DBUS_ADDR_MATCHING_1_REG_RESVAL 0x0

//   See !!IBUS_REMAP_ADDR_0 for a detailed description.
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_VAL_FIELD_WIDTH 32
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_MULTIREG_COUNT 2

//   See !!IBUS_REMAP_ADDR_0 for a detailed description.
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET 0x44
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_RESVAL 0x0

//   See !!IBUS_REMAP_ADDR_0 for a detailed description.
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_OFFSET 0x48
#define RV_CORE_IBEX_DBUS_REMAP_ADDR_1_REG_RESVAL 0x0

// Enable mask for NMI.
#define RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET 0x4c
#define RV_CORE_IBEX_NMI_ENABLE_REG_RESVAL 0x0
#define RV_CORE_IBEX_NMI_ENABLE_ALERT_EN_BIT 0
#define RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT 1

// Current NMI state
#define RV_CORE_IBEX_NMI_STATE_REG_OFFSET 0x50
#define RV_CORE_IBEX_NMI_STATE_REG_RESVAL 0x0
#define RV_CORE_IBEX_NMI_STATE_ALERT_BIT 0
#define RV_CORE_IBEX_NMI_STATE_WDOG_BIT 1

// error status
#define RV_CORE_IBEX_ERR_STATUS_REG_OFFSET 0x54
#define RV_CORE_IBEX_ERR_STATUS_REG_RESVAL 0x0
#define RV_CORE_IBEX_ERR_STATUS_REG_INTG_ERR_BIT 0
#define RV_CORE_IBEX_ERR_STATUS_FATAL_INTG_ERR_BIT 8
#define RV_CORE_IBEX_ERR_STATUS_FATAL_CORE_ERR_BIT 9
#define RV_CORE_IBEX_ERR_STATUS_RECOV_CORE_ERR_BIT 10

// Random data from EDN
#define RV_CORE_IBEX_RND_DATA_REG_OFFSET 0x58
#define RV_CORE_IBEX_RND_DATA_REG_RESVAL 0x0

// Status of random data in !!RND_DATA
#define RV_CORE_IBEX_RND_STATUS_REG_OFFSET 0x5c
#define RV_CORE_IBEX_RND_STATUS_REG_RESVAL 0x0
#define RV_CORE_IBEX_RND_STATUS_RND_DATA_VALID_BIT 0
#define RV_CORE_IBEX_RND_STATUS_RND_DATA_FIPS_BIT 1

// FPGA build timestamp info.
#define RV_CORE_IBEX_FPGA_INFO_REG_OFFSET 0x60
#define RV_CORE_IBEX_FPGA_INFO_REG_RESVAL 0x0

// Memory area: Exposed tlul window for DV only purposes.
#define RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET 0x80
#define RV_CORE_IBEX_DV_SIM_WINDOW_SIZE_WORDS 8
#define RV_CORE_IBEX_DV_SIM_WINDOW_SIZE_BYTES 32
#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _RV_CORE_IBEX_REG_DEFS_
// End generated register defines for RV_CORE_IBEX