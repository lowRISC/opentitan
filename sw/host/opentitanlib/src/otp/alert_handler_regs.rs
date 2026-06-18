// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Number of alert channels.
pub const ALERT_HANDLER_PARAM_N_ALERTS: u32 = 68;

// Number of LPGs.
pub const ALERT_HANDLER_PARAM_N_LPG: u32 = 24;

// Width of LPG ID.
pub const ALERT_HANDLER_PARAM_N_LPG_WIDTH: u32 = 5;

// Width of the escalation timer.
pub const ALERT_HANDLER_PARAM_ESC_CNT_DW: u32 = 32;

// Width of the accumulation counter.
pub const ALERT_HANDLER_PARAM_ACCU_CNT_DW: u32 = 16;

// Number of classes
pub const ALERT_HANDLER_PARAM_N_CLASSES: u32 = 4;

// Number of escalation severities
pub const ALERT_HANDLER_PARAM_N_ESC_SEV: u32 = 4;

// Number of escalation phases
pub const ALERT_HANDLER_PARAM_N_PHASES: u32 = 4;

// Number of local alerts
pub const ALERT_HANDLER_PARAM_N_LOC_ALERT: u32 = 7;

// Width of ping counter
pub const ALERT_HANDLER_PARAM_PING_CNT_DW: u32 = 16;

// Width of phase ID
pub const ALERT_HANDLER_PARAM_PHASE_DW: u32 = 2;

// Width of class ID
pub const ALERT_HANDLER_PARAM_CLASS_DW: u32 = 2;

// Local alert ID for alert ping failure.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_ALERT_PINGFAIL: u32 = 0;

// Local alert ID for escalation ping failure.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_ESC_PINGFAIL: u32 = 1;

// Local alert ID for alert integrity failure.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_ALERT_INTEGFAIL: u32 = 2;

// Local alert ID for escalation integrity failure.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_ESC_INTEGFAIL: u32 = 3;

// Local alert ID for bus integrity failure.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_BUS_INTEGFAIL: u32 = 4;

// Local alert ID for shadow register update error.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_SHADOW_REG_UPDATE_ERROR: u32 = 5;

// Local alert ID for shadow register storage error.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_SHADOW_REG_STORAGE_ERROR: u32 = 6;

// Last local alert ID.
pub const ALERT_HANDLER_PARAM_LOCAL_ALERT_ID_LAST: u32 = 6;

// Register width
pub const ALERT_HANDLER_PARAM_REG_WIDTH: u32 = 32;

// Common Interrupt Offsets
pub const ALERT_HANDLER_INTR_COMMON_CLASSA_BIT: u32 = 0;
pub const ALERT_HANDLER_INTR_COMMON_CLASSB_BIT: u32 = 1;
pub const ALERT_HANDLER_INTR_COMMON_CLASSC_BIT: u32 = 2;
pub const ALERT_HANDLER_INTR_COMMON_CLASSD_BIT: u32 = 3;

// Interrupt State Register
pub const ALERT_HANDLER_INTR_STATE_REG_OFFSET: usize = 0x0;
pub const ALERT_HANDLER_INTR_STATE_CLASSA_BIT: u32 = 0;
pub const ALERT_HANDLER_INTR_STATE_CLASSB_BIT: u32 = 1;
pub const ALERT_HANDLER_INTR_STATE_CLASSC_BIT: u32 = 2;
pub const ALERT_HANDLER_INTR_STATE_CLASSD_BIT: u32 = 3;

// Interrupt Enable Register
pub const ALERT_HANDLER_INTR_ENABLE_REG_OFFSET: usize = 0x4;
pub const ALERT_HANDLER_INTR_ENABLE_CLASSA_BIT: u32 = 0;
pub const ALERT_HANDLER_INTR_ENABLE_CLASSB_BIT: u32 = 1;
pub const ALERT_HANDLER_INTR_ENABLE_CLASSC_BIT: u32 = 2;
pub const ALERT_HANDLER_INTR_ENABLE_CLASSD_BIT: u32 = 3;

// Interrupt Test Register
pub const ALERT_HANDLER_INTR_TEST_REG_OFFSET: usize = 0x8;
pub const ALERT_HANDLER_INTR_TEST_CLASSA_BIT: u32 = 0;
pub const ALERT_HANDLER_INTR_TEST_CLASSB_BIT: u32 = 1;
pub const ALERT_HANDLER_INTR_TEST_CLASSC_BIT: u32 = 2;
pub const ALERT_HANDLER_INTR_TEST_CLASSD_BIT: u32 = 3;

// Register write enable for !!PING_TIMEOUT_CYC_SHADOWED and
// !!PING_TIMER_EN_SHADOWED.
pub const ALERT_HANDLER_PING_TIMER_REGWEN_REG_OFFSET: usize = 0xc;
pub const ALERT_HANDLER_PING_TIMER_REGWEN_PING_TIMER_REGWEN_BIT: u32 = 0;

// Ping timeout cycle count.
pub const ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_REG_OFFSET: usize = 0x10;
pub const ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK: u32 = 0xffff;
pub const ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_OFFSET: usize = 0;

// Ping timer enable.
pub const ALERT_HANDLER_PING_TIMER_EN_SHADOWED_REG_OFFSET: usize = 0x14;
pub const ALERT_HANDLER_PING_TIMER_EN_SHADOWED_PING_TIMER_EN_SHADOWED_BIT: u32 = 0;

// Register write enable for alert enable bits. (common parameters)
pub const ALERT_HANDLER_ALERT_REGWEN_EN_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_ALERT_REGWEN_EN_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_ALERT_REGWEN_MULTIREG_COUNT: u32 = 68;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_0_REG_OFFSET: usize = 0x18;
pub const ALERT_HANDLER_ALERT_REGWEN_0_EN_0_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_1_REG_OFFSET: usize = 0x1c;
pub const ALERT_HANDLER_ALERT_REGWEN_1_EN_1_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_2_REG_OFFSET: usize = 0x20;
pub const ALERT_HANDLER_ALERT_REGWEN_2_EN_2_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_3_REG_OFFSET: usize = 0x24;
pub const ALERT_HANDLER_ALERT_REGWEN_3_EN_3_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_4_REG_OFFSET: usize = 0x28;
pub const ALERT_HANDLER_ALERT_REGWEN_4_EN_4_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_5_REG_OFFSET: usize = 0x2c;
pub const ALERT_HANDLER_ALERT_REGWEN_5_EN_5_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_6_REG_OFFSET: usize = 0x30;
pub const ALERT_HANDLER_ALERT_REGWEN_6_EN_6_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_7_REG_OFFSET: usize = 0x34;
pub const ALERT_HANDLER_ALERT_REGWEN_7_EN_7_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_8_REG_OFFSET: usize = 0x38;
pub const ALERT_HANDLER_ALERT_REGWEN_8_EN_8_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_9_REG_OFFSET: usize = 0x3c;
pub const ALERT_HANDLER_ALERT_REGWEN_9_EN_9_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_10_REG_OFFSET: usize = 0x40;
pub const ALERT_HANDLER_ALERT_REGWEN_10_EN_10_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_11_REG_OFFSET: usize = 0x44;
pub const ALERT_HANDLER_ALERT_REGWEN_11_EN_11_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_12_REG_OFFSET: usize = 0x48;
pub const ALERT_HANDLER_ALERT_REGWEN_12_EN_12_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_13_REG_OFFSET: usize = 0x4c;
pub const ALERT_HANDLER_ALERT_REGWEN_13_EN_13_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_14_REG_OFFSET: usize = 0x50;
pub const ALERT_HANDLER_ALERT_REGWEN_14_EN_14_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_15_REG_OFFSET: usize = 0x54;
pub const ALERT_HANDLER_ALERT_REGWEN_15_EN_15_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_16_REG_OFFSET: usize = 0x58;
pub const ALERT_HANDLER_ALERT_REGWEN_16_EN_16_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_17_REG_OFFSET: usize = 0x5c;
pub const ALERT_HANDLER_ALERT_REGWEN_17_EN_17_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_18_REG_OFFSET: usize = 0x60;
pub const ALERT_HANDLER_ALERT_REGWEN_18_EN_18_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_19_REG_OFFSET: usize = 0x64;
pub const ALERT_HANDLER_ALERT_REGWEN_19_EN_19_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_20_REG_OFFSET: usize = 0x68;
pub const ALERT_HANDLER_ALERT_REGWEN_20_EN_20_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_21_REG_OFFSET: usize = 0x6c;
pub const ALERT_HANDLER_ALERT_REGWEN_21_EN_21_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_22_REG_OFFSET: usize = 0x70;
pub const ALERT_HANDLER_ALERT_REGWEN_22_EN_22_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_23_REG_OFFSET: usize = 0x74;
pub const ALERT_HANDLER_ALERT_REGWEN_23_EN_23_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_24_REG_OFFSET: usize = 0x78;
pub const ALERT_HANDLER_ALERT_REGWEN_24_EN_24_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_25_REG_OFFSET: usize = 0x7c;
pub const ALERT_HANDLER_ALERT_REGWEN_25_EN_25_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_26_REG_OFFSET: usize = 0x80;
pub const ALERT_HANDLER_ALERT_REGWEN_26_EN_26_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_27_REG_OFFSET: usize = 0x84;
pub const ALERT_HANDLER_ALERT_REGWEN_27_EN_27_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_28_REG_OFFSET: usize = 0x88;
pub const ALERT_HANDLER_ALERT_REGWEN_28_EN_28_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_29_REG_OFFSET: usize = 0x8c;
pub const ALERT_HANDLER_ALERT_REGWEN_29_EN_29_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_30_REG_OFFSET: usize = 0x90;
pub const ALERT_HANDLER_ALERT_REGWEN_30_EN_30_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_31_REG_OFFSET: usize = 0x94;
pub const ALERT_HANDLER_ALERT_REGWEN_31_EN_31_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_32_REG_OFFSET: usize = 0x98;
pub const ALERT_HANDLER_ALERT_REGWEN_32_EN_32_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_33_REG_OFFSET: usize = 0x9c;
pub const ALERT_HANDLER_ALERT_REGWEN_33_EN_33_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_34_REG_OFFSET: usize = 0xa0;
pub const ALERT_HANDLER_ALERT_REGWEN_34_EN_34_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_35_REG_OFFSET: usize = 0xa4;
pub const ALERT_HANDLER_ALERT_REGWEN_35_EN_35_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_36_REG_OFFSET: usize = 0xa8;
pub const ALERT_HANDLER_ALERT_REGWEN_36_EN_36_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_37_REG_OFFSET: usize = 0xac;
pub const ALERT_HANDLER_ALERT_REGWEN_37_EN_37_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_38_REG_OFFSET: usize = 0xb0;
pub const ALERT_HANDLER_ALERT_REGWEN_38_EN_38_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_39_REG_OFFSET: usize = 0xb4;
pub const ALERT_HANDLER_ALERT_REGWEN_39_EN_39_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_40_REG_OFFSET: usize = 0xb8;
pub const ALERT_HANDLER_ALERT_REGWEN_40_EN_40_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_41_REG_OFFSET: usize = 0xbc;
pub const ALERT_HANDLER_ALERT_REGWEN_41_EN_41_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_42_REG_OFFSET: usize = 0xc0;
pub const ALERT_HANDLER_ALERT_REGWEN_42_EN_42_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_43_REG_OFFSET: usize = 0xc4;
pub const ALERT_HANDLER_ALERT_REGWEN_43_EN_43_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_44_REG_OFFSET: usize = 0xc8;
pub const ALERT_HANDLER_ALERT_REGWEN_44_EN_44_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_45_REG_OFFSET: usize = 0xcc;
pub const ALERT_HANDLER_ALERT_REGWEN_45_EN_45_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_46_REG_OFFSET: usize = 0xd0;
pub const ALERT_HANDLER_ALERT_REGWEN_46_EN_46_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_47_REG_OFFSET: usize = 0xd4;
pub const ALERT_HANDLER_ALERT_REGWEN_47_EN_47_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_48_REG_OFFSET: usize = 0xd8;
pub const ALERT_HANDLER_ALERT_REGWEN_48_EN_48_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_49_REG_OFFSET: usize = 0xdc;
pub const ALERT_HANDLER_ALERT_REGWEN_49_EN_49_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_50_REG_OFFSET: usize = 0xe0;
pub const ALERT_HANDLER_ALERT_REGWEN_50_EN_50_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_51_REG_OFFSET: usize = 0xe4;
pub const ALERT_HANDLER_ALERT_REGWEN_51_EN_51_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_52_REG_OFFSET: usize = 0xe8;
pub const ALERT_HANDLER_ALERT_REGWEN_52_EN_52_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_53_REG_OFFSET: usize = 0xec;
pub const ALERT_HANDLER_ALERT_REGWEN_53_EN_53_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_54_REG_OFFSET: usize = 0xf0;
pub const ALERT_HANDLER_ALERT_REGWEN_54_EN_54_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_55_REG_OFFSET: usize = 0xf4;
pub const ALERT_HANDLER_ALERT_REGWEN_55_EN_55_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_56_REG_OFFSET: usize = 0xf8;
pub const ALERT_HANDLER_ALERT_REGWEN_56_EN_56_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_57_REG_OFFSET: usize = 0xfc;
pub const ALERT_HANDLER_ALERT_REGWEN_57_EN_57_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_58_REG_OFFSET: usize = 0x100;
pub const ALERT_HANDLER_ALERT_REGWEN_58_EN_58_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_59_REG_OFFSET: usize = 0x104;
pub const ALERT_HANDLER_ALERT_REGWEN_59_EN_59_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_60_REG_OFFSET: usize = 0x108;
pub const ALERT_HANDLER_ALERT_REGWEN_60_EN_60_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_61_REG_OFFSET: usize = 0x10c;
pub const ALERT_HANDLER_ALERT_REGWEN_61_EN_61_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_62_REG_OFFSET: usize = 0x110;
pub const ALERT_HANDLER_ALERT_REGWEN_62_EN_62_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_63_REG_OFFSET: usize = 0x114;
pub const ALERT_HANDLER_ALERT_REGWEN_63_EN_63_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_64_REG_OFFSET: usize = 0x118;
pub const ALERT_HANDLER_ALERT_REGWEN_64_EN_64_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_65_REG_OFFSET: usize = 0x11c;
pub const ALERT_HANDLER_ALERT_REGWEN_65_EN_65_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_66_REG_OFFSET: usize = 0x120;
pub const ALERT_HANDLER_ALERT_REGWEN_66_EN_66_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_ALERT_REGWEN_67_REG_OFFSET: usize = 0x124;
pub const ALERT_HANDLER_ALERT_REGWEN_67_EN_67_BIT: u32 = 0;

// Enable register for alerts. (common parameters)
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_EN_A_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_EN_A_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_MULTIREG_COUNT: u32 = 68;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_0_REG_OFFSET: usize = 0x128;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_0_EN_A_0_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_1_REG_OFFSET: usize = 0x12c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_1_EN_A_1_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_2_REG_OFFSET: usize = 0x130;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_2_EN_A_2_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_3_REG_OFFSET: usize = 0x134;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_3_EN_A_3_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_4_REG_OFFSET: usize = 0x138;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_4_EN_A_4_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_5_REG_OFFSET: usize = 0x13c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_5_EN_A_5_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_6_REG_OFFSET: usize = 0x140;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_6_EN_A_6_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_7_REG_OFFSET: usize = 0x144;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_7_EN_A_7_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_8_REG_OFFSET: usize = 0x148;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_8_EN_A_8_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_9_REG_OFFSET: usize = 0x14c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_9_EN_A_9_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_10_REG_OFFSET: usize = 0x150;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_10_EN_A_10_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_11_REG_OFFSET: usize = 0x154;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_11_EN_A_11_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_12_REG_OFFSET: usize = 0x158;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_12_EN_A_12_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_13_REG_OFFSET: usize = 0x15c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_13_EN_A_13_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_14_REG_OFFSET: usize = 0x160;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_14_EN_A_14_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_15_REG_OFFSET: usize = 0x164;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_15_EN_A_15_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_16_REG_OFFSET: usize = 0x168;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_16_EN_A_16_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_17_REG_OFFSET: usize = 0x16c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_17_EN_A_17_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_18_REG_OFFSET: usize = 0x170;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_18_EN_A_18_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_19_REG_OFFSET: usize = 0x174;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_19_EN_A_19_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_20_REG_OFFSET: usize = 0x178;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_20_EN_A_20_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_21_REG_OFFSET: usize = 0x17c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_21_EN_A_21_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_22_REG_OFFSET: usize = 0x180;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_22_EN_A_22_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_23_REG_OFFSET: usize = 0x184;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_23_EN_A_23_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_24_REG_OFFSET: usize = 0x188;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_24_EN_A_24_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_25_REG_OFFSET: usize = 0x18c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_25_EN_A_25_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_26_REG_OFFSET: usize = 0x190;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_26_EN_A_26_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_27_REG_OFFSET: usize = 0x194;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_27_EN_A_27_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_28_REG_OFFSET: usize = 0x198;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_28_EN_A_28_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_29_REG_OFFSET: usize = 0x19c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_29_EN_A_29_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_30_REG_OFFSET: usize = 0x1a0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_30_EN_A_30_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_31_REG_OFFSET: usize = 0x1a4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_31_EN_A_31_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_32_REG_OFFSET: usize = 0x1a8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_32_EN_A_32_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_33_REG_OFFSET: usize = 0x1ac;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_33_EN_A_33_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_34_REG_OFFSET: usize = 0x1b0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_34_EN_A_34_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_35_REG_OFFSET: usize = 0x1b4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_35_EN_A_35_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_36_REG_OFFSET: usize = 0x1b8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_36_EN_A_36_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_37_REG_OFFSET: usize = 0x1bc;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_37_EN_A_37_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_38_REG_OFFSET: usize = 0x1c0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_38_EN_A_38_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_39_REG_OFFSET: usize = 0x1c4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_39_EN_A_39_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_40_REG_OFFSET: usize = 0x1c8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_40_EN_A_40_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_41_REG_OFFSET: usize = 0x1cc;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_41_EN_A_41_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_42_REG_OFFSET: usize = 0x1d0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_42_EN_A_42_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_43_REG_OFFSET: usize = 0x1d4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_43_EN_A_43_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_44_REG_OFFSET: usize = 0x1d8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_44_EN_A_44_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_45_REG_OFFSET: usize = 0x1dc;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_45_EN_A_45_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_46_REG_OFFSET: usize = 0x1e0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_46_EN_A_46_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_47_REG_OFFSET: usize = 0x1e4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_47_EN_A_47_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_48_REG_OFFSET: usize = 0x1e8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_48_EN_A_48_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_49_REG_OFFSET: usize = 0x1ec;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_49_EN_A_49_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_50_REG_OFFSET: usize = 0x1f0;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_50_EN_A_50_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_51_REG_OFFSET: usize = 0x1f4;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_51_EN_A_51_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_52_REG_OFFSET: usize = 0x1f8;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_52_EN_A_52_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_53_REG_OFFSET: usize = 0x1fc;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_53_EN_A_53_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_54_REG_OFFSET: usize = 0x200;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_54_EN_A_54_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_55_REG_OFFSET: usize = 0x204;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_55_EN_A_55_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_56_REG_OFFSET: usize = 0x208;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_56_EN_A_56_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_57_REG_OFFSET: usize = 0x20c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_57_EN_A_57_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_58_REG_OFFSET: usize = 0x210;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_58_EN_A_58_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_59_REG_OFFSET: usize = 0x214;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_59_EN_A_59_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_60_REG_OFFSET: usize = 0x218;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_60_EN_A_60_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_61_REG_OFFSET: usize = 0x21c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_61_EN_A_61_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_62_REG_OFFSET: usize = 0x220;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_62_EN_A_62_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_63_REG_OFFSET: usize = 0x224;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_63_EN_A_63_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_64_REG_OFFSET: usize = 0x228;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_64_EN_A_64_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_65_REG_OFFSET: usize = 0x22c;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_65_EN_A_65_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_66_REG_OFFSET: usize = 0x230;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_66_EN_A_66_BIT: u32 = 0;

// Enable register for alerts.
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_67_REG_OFFSET: usize = 0x234;
pub const ALERT_HANDLER_ALERT_EN_SHADOWED_67_EN_A_67_BIT: u32 = 0;

// Class assignment of alerts. (common parameters)
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_CLASS_A_FIELD_WIDTH: u32 = 2;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_CLASS_A_FIELDS_PER_REG: u32 = 16;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_MULTIREG_COUNT: u32 = 68;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_REG_OFFSET: usize = 0x238;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_OFFSET: usize = 0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSA: u32 = 0x0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSB: u32 = 0x1;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSC: u32 = 0x2;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_0_CLASS_A_0_VALUE_CLASSD: u32 = 0x3;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_1_REG_OFFSET: usize = 0x23c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_1_CLASS_A_1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_1_CLASS_A_1_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_2_REG_OFFSET: usize = 0x240;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_2_CLASS_A_2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_2_CLASS_A_2_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_3_REG_OFFSET: usize = 0x244;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_3_CLASS_A_3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_3_CLASS_A_3_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_4_REG_OFFSET: usize = 0x248;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_4_CLASS_A_4_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_4_CLASS_A_4_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_5_REG_OFFSET: usize = 0x24c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_5_CLASS_A_5_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_5_CLASS_A_5_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_6_REG_OFFSET: usize = 0x250;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_6_CLASS_A_6_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_6_CLASS_A_6_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_7_REG_OFFSET: usize = 0x254;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_7_CLASS_A_7_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_7_CLASS_A_7_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_8_REG_OFFSET: usize = 0x258;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_8_CLASS_A_8_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_8_CLASS_A_8_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_9_REG_OFFSET: usize = 0x25c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_9_CLASS_A_9_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_9_CLASS_A_9_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_10_REG_OFFSET: usize = 0x260;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_10_CLASS_A_10_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_10_CLASS_A_10_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_11_REG_OFFSET: usize = 0x264;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_11_CLASS_A_11_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_11_CLASS_A_11_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_12_REG_OFFSET: usize = 0x268;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_12_CLASS_A_12_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_12_CLASS_A_12_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_13_REG_OFFSET: usize = 0x26c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_13_CLASS_A_13_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_13_CLASS_A_13_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_14_REG_OFFSET: usize = 0x270;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_14_CLASS_A_14_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_14_CLASS_A_14_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_15_REG_OFFSET: usize = 0x274;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_15_CLASS_A_15_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_15_CLASS_A_15_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_16_REG_OFFSET: usize = 0x278;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_16_CLASS_A_16_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_16_CLASS_A_16_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_17_REG_OFFSET: usize = 0x27c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_17_CLASS_A_17_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_17_CLASS_A_17_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_18_REG_OFFSET: usize = 0x280;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_18_CLASS_A_18_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_18_CLASS_A_18_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_19_REG_OFFSET: usize = 0x284;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_19_CLASS_A_19_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_19_CLASS_A_19_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_20_REG_OFFSET: usize = 0x288;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_20_CLASS_A_20_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_20_CLASS_A_20_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_21_REG_OFFSET: usize = 0x28c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_21_CLASS_A_21_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_21_CLASS_A_21_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_22_REG_OFFSET: usize = 0x290;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_22_CLASS_A_22_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_22_CLASS_A_22_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_23_REG_OFFSET: usize = 0x294;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_23_CLASS_A_23_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_23_CLASS_A_23_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_24_REG_OFFSET: usize = 0x298;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_24_CLASS_A_24_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_24_CLASS_A_24_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_25_REG_OFFSET: usize = 0x29c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_25_CLASS_A_25_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_25_CLASS_A_25_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_26_REG_OFFSET: usize = 0x2a0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_26_CLASS_A_26_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_26_CLASS_A_26_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_27_REG_OFFSET: usize = 0x2a4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_27_CLASS_A_27_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_27_CLASS_A_27_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_28_REG_OFFSET: usize = 0x2a8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_28_CLASS_A_28_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_28_CLASS_A_28_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_29_REG_OFFSET: usize = 0x2ac;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_29_CLASS_A_29_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_29_CLASS_A_29_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_30_REG_OFFSET: usize = 0x2b0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_30_CLASS_A_30_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_30_CLASS_A_30_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_31_REG_OFFSET: usize = 0x2b4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_31_CLASS_A_31_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_31_CLASS_A_31_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_32_REG_OFFSET: usize = 0x2b8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_32_CLASS_A_32_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_32_CLASS_A_32_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_33_REG_OFFSET: usize = 0x2bc;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_33_CLASS_A_33_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_33_CLASS_A_33_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_34_REG_OFFSET: usize = 0x2c0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_34_CLASS_A_34_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_34_CLASS_A_34_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_35_REG_OFFSET: usize = 0x2c4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_35_CLASS_A_35_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_35_CLASS_A_35_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_36_REG_OFFSET: usize = 0x2c8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_36_CLASS_A_36_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_36_CLASS_A_36_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_37_REG_OFFSET: usize = 0x2cc;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_37_CLASS_A_37_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_37_CLASS_A_37_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_38_REG_OFFSET: usize = 0x2d0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_38_CLASS_A_38_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_38_CLASS_A_38_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_39_REG_OFFSET: usize = 0x2d4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_39_CLASS_A_39_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_39_CLASS_A_39_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_40_REG_OFFSET: usize = 0x2d8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_40_CLASS_A_40_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_40_CLASS_A_40_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_41_REG_OFFSET: usize = 0x2dc;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_41_CLASS_A_41_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_41_CLASS_A_41_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_42_REG_OFFSET: usize = 0x2e0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_42_CLASS_A_42_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_42_CLASS_A_42_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_43_REG_OFFSET: usize = 0x2e4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_43_CLASS_A_43_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_43_CLASS_A_43_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_44_REG_OFFSET: usize = 0x2e8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_44_CLASS_A_44_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_44_CLASS_A_44_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_45_REG_OFFSET: usize = 0x2ec;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_45_CLASS_A_45_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_45_CLASS_A_45_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_46_REG_OFFSET: usize = 0x2f0;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_46_CLASS_A_46_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_46_CLASS_A_46_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_47_REG_OFFSET: usize = 0x2f4;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_47_CLASS_A_47_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_47_CLASS_A_47_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_48_REG_OFFSET: usize = 0x2f8;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_48_CLASS_A_48_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_48_CLASS_A_48_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_49_REG_OFFSET: usize = 0x2fc;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_49_CLASS_A_49_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_49_CLASS_A_49_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_50_REG_OFFSET: usize = 0x300;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_50_CLASS_A_50_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_50_CLASS_A_50_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_51_REG_OFFSET: usize = 0x304;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_51_CLASS_A_51_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_51_CLASS_A_51_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_52_REG_OFFSET: usize = 0x308;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_52_CLASS_A_52_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_52_CLASS_A_52_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_53_REG_OFFSET: usize = 0x30c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_53_CLASS_A_53_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_53_CLASS_A_53_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_54_REG_OFFSET: usize = 0x310;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_54_CLASS_A_54_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_54_CLASS_A_54_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_55_REG_OFFSET: usize = 0x314;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_55_CLASS_A_55_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_55_CLASS_A_55_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_56_REG_OFFSET: usize = 0x318;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_56_CLASS_A_56_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_56_CLASS_A_56_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_57_REG_OFFSET: usize = 0x31c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_57_CLASS_A_57_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_57_CLASS_A_57_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_58_REG_OFFSET: usize = 0x320;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_58_CLASS_A_58_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_58_CLASS_A_58_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_59_REG_OFFSET: usize = 0x324;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_59_CLASS_A_59_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_59_CLASS_A_59_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_60_REG_OFFSET: usize = 0x328;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_60_CLASS_A_60_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_60_CLASS_A_60_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_61_REG_OFFSET: usize = 0x32c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_61_CLASS_A_61_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_61_CLASS_A_61_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_62_REG_OFFSET: usize = 0x330;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_62_CLASS_A_62_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_62_CLASS_A_62_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_63_REG_OFFSET: usize = 0x334;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_63_CLASS_A_63_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_63_CLASS_A_63_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_64_REG_OFFSET: usize = 0x338;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_64_CLASS_A_64_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_64_CLASS_A_64_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_65_REG_OFFSET: usize = 0x33c;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_65_CLASS_A_65_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_65_CLASS_A_65_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_66_REG_OFFSET: usize = 0x340;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_66_CLASS_A_66_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_66_CLASS_A_66_OFFSET: usize = 0;

// Class assignment of alerts.
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_67_REG_OFFSET: usize = 0x344;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_67_CLASS_A_67_MASK: u32 = 0x3;
pub const ALERT_HANDLER_ALERT_CLASS_SHADOWED_67_CLASS_A_67_OFFSET: usize = 0;

// Alert Cause Register (common parameters)
pub const ALERT_HANDLER_ALERT_CAUSE_A_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_ALERT_CAUSE_A_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_ALERT_CAUSE_MULTIREG_COUNT: u32 = 68;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_0_REG_OFFSET: usize = 0x348;
pub const ALERT_HANDLER_ALERT_CAUSE_0_A_0_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_1_REG_OFFSET: usize = 0x34c;
pub const ALERT_HANDLER_ALERT_CAUSE_1_A_1_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_2_REG_OFFSET: usize = 0x350;
pub const ALERT_HANDLER_ALERT_CAUSE_2_A_2_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_3_REG_OFFSET: usize = 0x354;
pub const ALERT_HANDLER_ALERT_CAUSE_3_A_3_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_4_REG_OFFSET: usize = 0x358;
pub const ALERT_HANDLER_ALERT_CAUSE_4_A_4_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_5_REG_OFFSET: usize = 0x35c;
pub const ALERT_HANDLER_ALERT_CAUSE_5_A_5_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_6_REG_OFFSET: usize = 0x360;
pub const ALERT_HANDLER_ALERT_CAUSE_6_A_6_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_7_REG_OFFSET: usize = 0x364;
pub const ALERT_HANDLER_ALERT_CAUSE_7_A_7_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_8_REG_OFFSET: usize = 0x368;
pub const ALERT_HANDLER_ALERT_CAUSE_8_A_8_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_9_REG_OFFSET: usize = 0x36c;
pub const ALERT_HANDLER_ALERT_CAUSE_9_A_9_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_10_REG_OFFSET: usize = 0x370;
pub const ALERT_HANDLER_ALERT_CAUSE_10_A_10_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_11_REG_OFFSET: usize = 0x374;
pub const ALERT_HANDLER_ALERT_CAUSE_11_A_11_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_12_REG_OFFSET: usize = 0x378;
pub const ALERT_HANDLER_ALERT_CAUSE_12_A_12_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_13_REG_OFFSET: usize = 0x37c;
pub const ALERT_HANDLER_ALERT_CAUSE_13_A_13_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_14_REG_OFFSET: usize = 0x380;
pub const ALERT_HANDLER_ALERT_CAUSE_14_A_14_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_15_REG_OFFSET: usize = 0x384;
pub const ALERT_HANDLER_ALERT_CAUSE_15_A_15_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_16_REG_OFFSET: usize = 0x388;
pub const ALERT_HANDLER_ALERT_CAUSE_16_A_16_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_17_REG_OFFSET: usize = 0x38c;
pub const ALERT_HANDLER_ALERT_CAUSE_17_A_17_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_18_REG_OFFSET: usize = 0x390;
pub const ALERT_HANDLER_ALERT_CAUSE_18_A_18_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_19_REG_OFFSET: usize = 0x394;
pub const ALERT_HANDLER_ALERT_CAUSE_19_A_19_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_20_REG_OFFSET: usize = 0x398;
pub const ALERT_HANDLER_ALERT_CAUSE_20_A_20_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_21_REG_OFFSET: usize = 0x39c;
pub const ALERT_HANDLER_ALERT_CAUSE_21_A_21_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_22_REG_OFFSET: usize = 0x3a0;
pub const ALERT_HANDLER_ALERT_CAUSE_22_A_22_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_23_REG_OFFSET: usize = 0x3a4;
pub const ALERT_HANDLER_ALERT_CAUSE_23_A_23_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_24_REG_OFFSET: usize = 0x3a8;
pub const ALERT_HANDLER_ALERT_CAUSE_24_A_24_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_25_REG_OFFSET: usize = 0x3ac;
pub const ALERT_HANDLER_ALERT_CAUSE_25_A_25_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_26_REG_OFFSET: usize = 0x3b0;
pub const ALERT_HANDLER_ALERT_CAUSE_26_A_26_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_27_REG_OFFSET: usize = 0x3b4;
pub const ALERT_HANDLER_ALERT_CAUSE_27_A_27_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_28_REG_OFFSET: usize = 0x3b8;
pub const ALERT_HANDLER_ALERT_CAUSE_28_A_28_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_29_REG_OFFSET: usize = 0x3bc;
pub const ALERT_HANDLER_ALERT_CAUSE_29_A_29_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_30_REG_OFFSET: usize = 0x3c0;
pub const ALERT_HANDLER_ALERT_CAUSE_30_A_30_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_31_REG_OFFSET: usize = 0x3c4;
pub const ALERT_HANDLER_ALERT_CAUSE_31_A_31_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_32_REG_OFFSET: usize = 0x3c8;
pub const ALERT_HANDLER_ALERT_CAUSE_32_A_32_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_33_REG_OFFSET: usize = 0x3cc;
pub const ALERT_HANDLER_ALERT_CAUSE_33_A_33_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_34_REG_OFFSET: usize = 0x3d0;
pub const ALERT_HANDLER_ALERT_CAUSE_34_A_34_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_35_REG_OFFSET: usize = 0x3d4;
pub const ALERT_HANDLER_ALERT_CAUSE_35_A_35_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_36_REG_OFFSET: usize = 0x3d8;
pub const ALERT_HANDLER_ALERT_CAUSE_36_A_36_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_37_REG_OFFSET: usize = 0x3dc;
pub const ALERT_HANDLER_ALERT_CAUSE_37_A_37_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_38_REG_OFFSET: usize = 0x3e0;
pub const ALERT_HANDLER_ALERT_CAUSE_38_A_38_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_39_REG_OFFSET: usize = 0x3e4;
pub const ALERT_HANDLER_ALERT_CAUSE_39_A_39_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_40_REG_OFFSET: usize = 0x3e8;
pub const ALERT_HANDLER_ALERT_CAUSE_40_A_40_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_41_REG_OFFSET: usize = 0x3ec;
pub const ALERT_HANDLER_ALERT_CAUSE_41_A_41_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_42_REG_OFFSET: usize = 0x3f0;
pub const ALERT_HANDLER_ALERT_CAUSE_42_A_42_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_43_REG_OFFSET: usize = 0x3f4;
pub const ALERT_HANDLER_ALERT_CAUSE_43_A_43_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_44_REG_OFFSET: usize = 0x3f8;
pub const ALERT_HANDLER_ALERT_CAUSE_44_A_44_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_45_REG_OFFSET: usize = 0x3fc;
pub const ALERT_HANDLER_ALERT_CAUSE_45_A_45_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_46_REG_OFFSET: usize = 0x400;
pub const ALERT_HANDLER_ALERT_CAUSE_46_A_46_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_47_REG_OFFSET: usize = 0x404;
pub const ALERT_HANDLER_ALERT_CAUSE_47_A_47_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_48_REG_OFFSET: usize = 0x408;
pub const ALERT_HANDLER_ALERT_CAUSE_48_A_48_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_49_REG_OFFSET: usize = 0x40c;
pub const ALERT_HANDLER_ALERT_CAUSE_49_A_49_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_50_REG_OFFSET: usize = 0x410;
pub const ALERT_HANDLER_ALERT_CAUSE_50_A_50_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_51_REG_OFFSET: usize = 0x414;
pub const ALERT_HANDLER_ALERT_CAUSE_51_A_51_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_52_REG_OFFSET: usize = 0x418;
pub const ALERT_HANDLER_ALERT_CAUSE_52_A_52_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_53_REG_OFFSET: usize = 0x41c;
pub const ALERT_HANDLER_ALERT_CAUSE_53_A_53_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_54_REG_OFFSET: usize = 0x420;
pub const ALERT_HANDLER_ALERT_CAUSE_54_A_54_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_55_REG_OFFSET: usize = 0x424;
pub const ALERT_HANDLER_ALERT_CAUSE_55_A_55_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_56_REG_OFFSET: usize = 0x428;
pub const ALERT_HANDLER_ALERT_CAUSE_56_A_56_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_57_REG_OFFSET: usize = 0x42c;
pub const ALERT_HANDLER_ALERT_CAUSE_57_A_57_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_58_REG_OFFSET: usize = 0x430;
pub const ALERT_HANDLER_ALERT_CAUSE_58_A_58_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_59_REG_OFFSET: usize = 0x434;
pub const ALERT_HANDLER_ALERT_CAUSE_59_A_59_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_60_REG_OFFSET: usize = 0x438;
pub const ALERT_HANDLER_ALERT_CAUSE_60_A_60_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_61_REG_OFFSET: usize = 0x43c;
pub const ALERT_HANDLER_ALERT_CAUSE_61_A_61_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_62_REG_OFFSET: usize = 0x440;
pub const ALERT_HANDLER_ALERT_CAUSE_62_A_62_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_63_REG_OFFSET: usize = 0x444;
pub const ALERT_HANDLER_ALERT_CAUSE_63_A_63_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_64_REG_OFFSET: usize = 0x448;
pub const ALERT_HANDLER_ALERT_CAUSE_64_A_64_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_65_REG_OFFSET: usize = 0x44c;
pub const ALERT_HANDLER_ALERT_CAUSE_65_A_65_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_66_REG_OFFSET: usize = 0x450;
pub const ALERT_HANDLER_ALERT_CAUSE_66_A_66_BIT: u32 = 0;

// Alert Cause Register
pub const ALERT_HANDLER_ALERT_CAUSE_67_REG_OFFSET: usize = 0x454;
pub const ALERT_HANDLER_ALERT_CAUSE_67_A_67_BIT: u32 = 0;

// Register write enable for alert enable bits. (common parameters)
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_EN_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_EN_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_MULTIREG_COUNT: u32 = 7;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_0_REG_OFFSET: usize = 0x458;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_0_EN_0_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_1_REG_OFFSET: usize = 0x45c;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_1_EN_1_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_2_REG_OFFSET: usize = 0x460;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_2_EN_2_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_3_REG_OFFSET: usize = 0x464;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_3_EN_3_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_4_REG_OFFSET: usize = 0x468;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_4_EN_4_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_5_REG_OFFSET: usize = 0x46c;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_5_EN_5_BIT: u32 = 0;

// Register write enable for alert enable bits.
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_6_REG_OFFSET: usize = 0x470;
pub const ALERT_HANDLER_LOC_ALERT_REGWEN_6_EN_6_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_EN_LA_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_EN_LA_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_MULTIREG_COUNT: u32 = 7;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_REG_OFFSET: usize = 0x474;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_0_EN_LA_0_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_REG_OFFSET: usize = 0x478;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_1_EN_LA_1_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_REG_OFFSET: usize = 0x47c;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_2_EN_LA_2_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_3_REG_OFFSET: usize = 0x480;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_3_EN_LA_3_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_4_REG_OFFSET: usize = 0x484;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_4_EN_LA_4_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_5_REG_OFFSET: usize = 0x488;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_5_EN_LA_5_BIT: u32 = 0;

// Enable register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_6_REG_OFFSET: usize = 0x48c;
pub const ALERT_HANDLER_LOC_ALERT_EN_SHADOWED_6_EN_LA_6_BIT: u32 = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_CLASS_LA_FIELD_WIDTH: u32 = 2;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_CLASS_LA_FIELDS_PER_REG: u32 = 16;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_MULTIREG_COUNT: u32 = 7;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_REG_OFFSET: usize = 0x490;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_OFFSET: usize = 0;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSA: u32 = 0x0;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSB: u32 = 0x1;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSC: u32 = 0x2;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_0_CLASS_LA_0_VALUE_CLASSD: u32 = 0x3;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_REG_OFFSET: usize = 0x494;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_CLASS_LA_1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_1_CLASS_LA_1_OFFSET: usize = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_REG_OFFSET: usize = 0x498;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_CLASS_LA_2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_2_CLASS_LA_2_OFFSET: usize = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_REG_OFFSET: usize = 0x49c;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_CLASS_LA_3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_3_CLASS_LA_3_OFFSET: usize = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_4_REG_OFFSET: usize = 0x4a0;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_4_CLASS_LA_4_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_4_CLASS_LA_4_OFFSET: usize = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_5_REG_OFFSET: usize = 0x4a4;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_5_CLASS_LA_5_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_5_CLASS_LA_5_OFFSET: usize = 0;

// Class assignment of the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_6_REG_OFFSET: usize = 0x4a8;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_6_CLASS_LA_6_MASK: u32 = 0x3;
pub const ALERT_HANDLER_LOC_ALERT_CLASS_SHADOWED_6_CLASS_LA_6_OFFSET: usize = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_LA_FIELD_WIDTH: u32 = 1;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_LA_FIELDS_PER_REG: u32 = 32;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_MULTIREG_COUNT: u32 = 7;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_0_REG_OFFSET: usize = 0x4ac;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_0_LA_0_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_1_REG_OFFSET: usize = 0x4b0;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_1_LA_1_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_2_REG_OFFSET: usize = 0x4b4;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_2_LA_2_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_3_REG_OFFSET: usize = 0x4b8;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_3_LA_3_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_4_REG_OFFSET: usize = 0x4bc;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_4_LA_4_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_5_REG_OFFSET: usize = 0x4c0;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_5_LA_5_BIT: u32 = 0;

// Alert Cause Register for the local alerts
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_6_REG_OFFSET: usize = 0x4c4;
pub const ALERT_HANDLER_LOC_ALERT_CAUSE_6_LA_6_BIT: u32 = 0;

// Lock bit for Class A configuration.
pub const ALERT_HANDLER_CLASSA_REGWEN_REG_OFFSET: usize = 0x4c8;
pub const ALERT_HANDLER_CLASSA_REGWEN_CLASSA_REGWEN_BIT: u32 = 0;

// Escalation control register for alert Class A. Can not be modified if
// !!CLASSA_REGWEN is false.
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_REG_OFFSET: usize = 0x4cc;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_BIT: u32 = 0;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_LOCK_BIT: u32 = 1;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E0_BIT: u32 = 2;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E1_BIT: u32 = 3;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E2_BIT: u32 = 4;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_EN_E3_BIT: u32 = 5;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E0_OFFSET: usize = 6;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E1_OFFSET: usize = 8;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E2_OFFSET: usize = 10;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_CTRL_SHADOWED_MAP_E3_OFFSET: usize = 12;

// Clear enable for escalation protocol of Class A alerts.
pub const ALERT_HANDLER_CLASSA_CLR_REGWEN_REG_OFFSET: usize = 0x4d0;
pub const ALERT_HANDLER_CLASSA_CLR_REGWEN_CLASSA_CLR_REGWEN_BIT: u32 = 0;

// Clear for escalation protocol of Class A.
pub const ALERT_HANDLER_CLASSA_CLR_SHADOWED_REG_OFFSET: usize = 0x4d4;
pub const ALERT_HANDLER_CLASSA_CLR_SHADOWED_CLASSA_CLR_SHADOWED_BIT: u32 = 0;

// Current accumulation value for alert Class A. Software can clear this
// register
pub const ALERT_HANDLER_CLASSA_ACCUM_CNT_REG_OFFSET: usize = 0x4d8;
pub const ALERT_HANDLER_CLASSA_ACCUM_CNT_CLASSA_ACCUM_CNT_MASK: u32 = 0xffff;
pub const ALERT_HANDLER_CLASSA_ACCUM_CNT_CLASSA_ACCUM_CNT_OFFSET: usize = 0;

// Accumulation threshold value for alert Class A.
pub const ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_REG_OFFSET: usize = 0x4dc;
pub const ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_CLASSA_ACCUM_THRESH_SHADOWED_MASK: u32 =
    0xffff;
pub const ALERT_HANDLER_CLASSA_ACCUM_THRESH_SHADOWED_CLASSA_ACCUM_THRESH_SHADOWED_OFFSET: usize = 0;

// Interrupt timeout in cycles.
pub const ALERT_HANDLER_CLASSA_TIMEOUT_CYC_SHADOWED_REG_OFFSET: usize = 0x4e0;

// Crashdump trigger configuration for Class A.
pub const ALERT_HANDLER_CLASSA_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET: usize = 0x4e4;
pub const ALERT_HANDLER_CLASSA_CRASHDUMP_TRIGGER_SHADOWED_CLASSA_CRASHDUMP_TRIGGER_SHADOWED_MASK:
    u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_CRASHDUMP_TRIGGER_SHADOWED_CLASSA_CRASHDUMP_TRIGGER_SHADOWED_OFFSET: usize = 0;

// Duration of escalation phase 0 for Class A.
pub const ALERT_HANDLER_CLASSA_PHASE0_CYC_SHADOWED_REG_OFFSET: usize = 0x4e8;

// Duration of escalation phase 1 for Class A.
pub const ALERT_HANDLER_CLASSA_PHASE1_CYC_SHADOWED_REG_OFFSET: usize = 0x4ec;

// Duration of escalation phase 2 for Class A.
pub const ALERT_HANDLER_CLASSA_PHASE2_CYC_SHADOWED_REG_OFFSET: usize = 0x4f0;

// Duration of escalation phase 3 for Class A.
pub const ALERT_HANDLER_CLASSA_PHASE3_CYC_SHADOWED_REG_OFFSET: usize = 0x4f4;

// Escalation counter in cycles for Class A.
pub const ALERT_HANDLER_CLASSA_ESC_CNT_REG_OFFSET: usize = 0x4f8;

// Current escalation state of Class A. See also !!CLASSA_ESC_CNT.
pub const ALERT_HANDLER_CLASSA_STATE_REG_OFFSET: usize = 0x4fc;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_MASK: u32 = 0x7;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_OFFSET: usize = 0;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_IDLE: u32 = 0x0;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TIMEOUT: u32 = 0x1;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_FSMERROR: u32 = 0x2;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_TERMINAL: u32 = 0x3;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE0: u32 = 0x4;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE1: u32 = 0x5;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE2: u32 = 0x6;
pub const ALERT_HANDLER_CLASSA_STATE_CLASSA_STATE_VALUE_PHASE3: u32 = 0x7;

// Lock bit for Class B configuration.
pub const ALERT_HANDLER_CLASSB_REGWEN_REG_OFFSET: usize = 0x500;
pub const ALERT_HANDLER_CLASSB_REGWEN_CLASSB_REGWEN_BIT: u32 = 0;

// Escalation control register for alert Class B. Can not be modified if
// !!CLASSB_REGWEN is false.
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_REG_OFFSET: usize = 0x504;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_BIT: u32 = 0;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_LOCK_BIT: u32 = 1;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_E0_BIT: u32 = 2;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_E1_BIT: u32 = 3;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_E2_BIT: u32 = 4;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_EN_E3_BIT: u32 = 5;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E0_OFFSET: usize = 6;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E1_OFFSET: usize = 8;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E2_OFFSET: usize = 10;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_CTRL_SHADOWED_MAP_E3_OFFSET: usize = 12;

// Clear enable for escalation protocol of Class B alerts.
pub const ALERT_HANDLER_CLASSB_CLR_REGWEN_REG_OFFSET: usize = 0x508;
pub const ALERT_HANDLER_CLASSB_CLR_REGWEN_CLASSB_CLR_REGWEN_BIT: u32 = 0;

// Clear for escalation protocol of Class B.
pub const ALERT_HANDLER_CLASSB_CLR_SHADOWED_REG_OFFSET: usize = 0x50c;
pub const ALERT_HANDLER_CLASSB_CLR_SHADOWED_CLASSB_CLR_SHADOWED_BIT: u32 = 0;

// Current accumulation value for alert Class B. Software can clear this
// register
pub const ALERT_HANDLER_CLASSB_ACCUM_CNT_REG_OFFSET: usize = 0x510;
pub const ALERT_HANDLER_CLASSB_ACCUM_CNT_CLASSB_ACCUM_CNT_MASK: u32 = 0xffff;
pub const ALERT_HANDLER_CLASSB_ACCUM_CNT_CLASSB_ACCUM_CNT_OFFSET: usize = 0;

// Accumulation threshold value for alert Class B.
pub const ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_REG_OFFSET: usize = 0x514;
pub const ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_CLASSB_ACCUM_THRESH_SHADOWED_MASK: u32 =
    0xffff;
pub const ALERT_HANDLER_CLASSB_ACCUM_THRESH_SHADOWED_CLASSB_ACCUM_THRESH_SHADOWED_OFFSET: usize = 0;

// Interrupt timeout in cycles.
pub const ALERT_HANDLER_CLASSB_TIMEOUT_CYC_SHADOWED_REG_OFFSET: usize = 0x518;

// Crashdump trigger configuration for Class B.
pub const ALERT_HANDLER_CLASSB_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET: usize = 0x51c;
pub const ALERT_HANDLER_CLASSB_CRASHDUMP_TRIGGER_SHADOWED_CLASSB_CRASHDUMP_TRIGGER_SHADOWED_MASK:
    u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_CRASHDUMP_TRIGGER_SHADOWED_CLASSB_CRASHDUMP_TRIGGER_SHADOWED_OFFSET: usize = 0;

// Duration of escalation phase 0 for Class B.
pub const ALERT_HANDLER_CLASSB_PHASE0_CYC_SHADOWED_REG_OFFSET: usize = 0x520;

// Duration of escalation phase 1 for Class B.
pub const ALERT_HANDLER_CLASSB_PHASE1_CYC_SHADOWED_REG_OFFSET: usize = 0x524;

// Duration of escalation phase 2 for Class B.
pub const ALERT_HANDLER_CLASSB_PHASE2_CYC_SHADOWED_REG_OFFSET: usize = 0x528;

// Duration of escalation phase 3 for Class B.
pub const ALERT_HANDLER_CLASSB_PHASE3_CYC_SHADOWED_REG_OFFSET: usize = 0x52c;

// Escalation counter in cycles for Class B.
pub const ALERT_HANDLER_CLASSB_ESC_CNT_REG_OFFSET: usize = 0x530;

// Current escalation state of Class B. See also !!CLASSB_ESC_CNT.
pub const ALERT_HANDLER_CLASSB_STATE_REG_OFFSET: usize = 0x534;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_MASK: u32 = 0x7;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_OFFSET: usize = 0;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_IDLE: u32 = 0x0;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_TIMEOUT: u32 = 0x1;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_FSMERROR: u32 = 0x2;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_TERMINAL: u32 = 0x3;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_PHASE0: u32 = 0x4;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_PHASE1: u32 = 0x5;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_PHASE2: u32 = 0x6;
pub const ALERT_HANDLER_CLASSB_STATE_CLASSB_STATE_VALUE_PHASE3: u32 = 0x7;

// Lock bit for Class C configuration.
pub const ALERT_HANDLER_CLASSC_REGWEN_REG_OFFSET: usize = 0x538;
pub const ALERT_HANDLER_CLASSC_REGWEN_CLASSC_REGWEN_BIT: u32 = 0;

// Escalation control register for alert Class C. Can not be modified if
// !!CLASSC_REGWEN is false.
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_REG_OFFSET: usize = 0x53c;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_BIT: u32 = 0;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_LOCK_BIT: u32 = 1;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E0_BIT: u32 = 2;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E1_BIT: u32 = 3;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E2_BIT: u32 = 4;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_EN_E3_BIT: u32 = 5;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E0_OFFSET: usize = 6;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E1_OFFSET: usize = 8;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E2_OFFSET: usize = 10;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_CTRL_SHADOWED_MAP_E3_OFFSET: usize = 12;

// Clear enable for escalation protocol of Class C alerts.
pub const ALERT_HANDLER_CLASSC_CLR_REGWEN_REG_OFFSET: usize = 0x540;
pub const ALERT_HANDLER_CLASSC_CLR_REGWEN_CLASSC_CLR_REGWEN_BIT: u32 = 0;

// Clear for escalation protocol of Class C.
pub const ALERT_HANDLER_CLASSC_CLR_SHADOWED_REG_OFFSET: usize = 0x544;
pub const ALERT_HANDLER_CLASSC_CLR_SHADOWED_CLASSC_CLR_SHADOWED_BIT: u32 = 0;

// Current accumulation value for alert Class C. Software can clear this
// register
pub const ALERT_HANDLER_CLASSC_ACCUM_CNT_REG_OFFSET: usize = 0x548;
pub const ALERT_HANDLER_CLASSC_ACCUM_CNT_CLASSC_ACCUM_CNT_MASK: u32 = 0xffff;
pub const ALERT_HANDLER_CLASSC_ACCUM_CNT_CLASSC_ACCUM_CNT_OFFSET: usize = 0;

// Accumulation threshold value for alert Class C.
pub const ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_REG_OFFSET: usize = 0x54c;
pub const ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_CLASSC_ACCUM_THRESH_SHADOWED_MASK: u32 =
    0xffff;
pub const ALERT_HANDLER_CLASSC_ACCUM_THRESH_SHADOWED_CLASSC_ACCUM_THRESH_SHADOWED_OFFSET: usize = 0;

// Interrupt timeout in cycles.
pub const ALERT_HANDLER_CLASSC_TIMEOUT_CYC_SHADOWED_REG_OFFSET: usize = 0x550;

// Crashdump trigger configuration for Class C.
pub const ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET: usize = 0x554;
pub const ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_MASK:
    u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_CLASSC_CRASHDUMP_TRIGGER_SHADOWED_OFFSET: usize = 0;

// Duration of escalation phase 0 for Class C.
pub const ALERT_HANDLER_CLASSC_PHASE0_CYC_SHADOWED_REG_OFFSET: usize = 0x558;

// Duration of escalation phase 1 for Class C.
pub const ALERT_HANDLER_CLASSC_PHASE1_CYC_SHADOWED_REG_OFFSET: usize = 0x55c;

// Duration of escalation phase 2 for Class C.
pub const ALERT_HANDLER_CLASSC_PHASE2_CYC_SHADOWED_REG_OFFSET: usize = 0x560;

// Duration of escalation phase 3 for Class C.
pub const ALERT_HANDLER_CLASSC_PHASE3_CYC_SHADOWED_REG_OFFSET: usize = 0x564;

// Escalation counter in cycles for Class C.
pub const ALERT_HANDLER_CLASSC_ESC_CNT_REG_OFFSET: usize = 0x568;

// Current escalation state of Class C. See also !!CLASSC_ESC_CNT.
pub const ALERT_HANDLER_CLASSC_STATE_REG_OFFSET: usize = 0x56c;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_MASK: u32 = 0x7;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_OFFSET: usize = 0;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_IDLE: u32 = 0x0;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_TIMEOUT: u32 = 0x1;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_FSMERROR: u32 = 0x2;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_TERMINAL: u32 = 0x3;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_PHASE0: u32 = 0x4;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_PHASE1: u32 = 0x5;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_PHASE2: u32 = 0x6;
pub const ALERT_HANDLER_CLASSC_STATE_CLASSC_STATE_VALUE_PHASE3: u32 = 0x7;

// Lock bit for Class D configuration.
pub const ALERT_HANDLER_CLASSD_REGWEN_REG_OFFSET: usize = 0x570;
pub const ALERT_HANDLER_CLASSD_REGWEN_CLASSD_REGWEN_BIT: u32 = 0;

// Escalation control register for alert Class D. Can not be modified if
// !!CLASSD_REGWEN is false.
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_REG_OFFSET: usize = 0x574;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_EN_BIT: u32 = 0;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_LOCK_BIT: u32 = 1;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_EN_E0_BIT: u32 = 2;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_EN_E1_BIT: u32 = 3;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_EN_E2_BIT: u32 = 4;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_EN_E3_BIT: u32 = 5;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E0_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E0_OFFSET: usize = 6;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E1_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E1_OFFSET: usize = 8;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E2_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E2_OFFSET: usize = 10;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E3_MASK: u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_CTRL_SHADOWED_MAP_E3_OFFSET: usize = 12;

// Clear enable for escalation protocol of Class D alerts.
pub const ALERT_HANDLER_CLASSD_CLR_REGWEN_REG_OFFSET: usize = 0x578;
pub const ALERT_HANDLER_CLASSD_CLR_REGWEN_CLASSD_CLR_REGWEN_BIT: u32 = 0;

// Clear for escalation protocol of Class D.
pub const ALERT_HANDLER_CLASSD_CLR_SHADOWED_REG_OFFSET: usize = 0x57c;
pub const ALERT_HANDLER_CLASSD_CLR_SHADOWED_CLASSD_CLR_SHADOWED_BIT: u32 = 0;

// Current accumulation value for alert Class D. Software can clear this
// register
pub const ALERT_HANDLER_CLASSD_ACCUM_CNT_REG_OFFSET: usize = 0x580;
pub const ALERT_HANDLER_CLASSD_ACCUM_CNT_CLASSD_ACCUM_CNT_MASK: u32 = 0xffff;
pub const ALERT_HANDLER_CLASSD_ACCUM_CNT_CLASSD_ACCUM_CNT_OFFSET: usize = 0;

// Accumulation threshold value for alert Class D.
pub const ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_REG_OFFSET: usize = 0x584;
pub const ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_CLASSD_ACCUM_THRESH_SHADOWED_MASK: u32 =
    0xffff;
pub const ALERT_HANDLER_CLASSD_ACCUM_THRESH_SHADOWED_CLASSD_ACCUM_THRESH_SHADOWED_OFFSET: usize = 0;

// Interrupt timeout in cycles.
pub const ALERT_HANDLER_CLASSD_TIMEOUT_CYC_SHADOWED_REG_OFFSET: usize = 0x588;

// Crashdump trigger configuration for Class D.
pub const ALERT_HANDLER_CLASSD_CRASHDUMP_TRIGGER_SHADOWED_REG_OFFSET: usize = 0x58c;
pub const ALERT_HANDLER_CLASSD_CRASHDUMP_TRIGGER_SHADOWED_CLASSD_CRASHDUMP_TRIGGER_SHADOWED_MASK:
    u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_CRASHDUMP_TRIGGER_SHADOWED_CLASSD_CRASHDUMP_TRIGGER_SHADOWED_OFFSET: usize = 0;

// Duration of escalation phase 0 for Class D.
pub const ALERT_HANDLER_CLASSD_PHASE0_CYC_SHADOWED_REG_OFFSET: usize = 0x590;

// Duration of escalation phase 1 for Class D.
pub const ALERT_HANDLER_CLASSD_PHASE1_CYC_SHADOWED_REG_OFFSET: usize = 0x594;

// Duration of escalation phase 2 for Class D.
pub const ALERT_HANDLER_CLASSD_PHASE2_CYC_SHADOWED_REG_OFFSET: usize = 0x598;

// Duration of escalation phase 3 for Class D.
pub const ALERT_HANDLER_CLASSD_PHASE3_CYC_SHADOWED_REG_OFFSET: usize = 0x59c;

// Escalation counter in cycles for Class D.
pub const ALERT_HANDLER_CLASSD_ESC_CNT_REG_OFFSET: usize = 0x5a0;

// Current escalation state of Class D. See also !!CLASSD_ESC_CNT.
pub const ALERT_HANDLER_CLASSD_STATE_REG_OFFSET: usize = 0x5a4;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_MASK: u32 = 0x7;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_OFFSET: usize = 0;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_IDLE: u32 = 0x0;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_TIMEOUT: u32 = 0x1;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_FSMERROR: u32 = 0x2;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_TERMINAL: u32 = 0x3;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_PHASE0: u32 = 0x4;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_PHASE1: u32 = 0x5;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_PHASE2: u32 = 0x6;
pub const ALERT_HANDLER_CLASSD_STATE_CLASSD_STATE_VALUE_PHASE3: u32 = 0x7;

// End generated register constants for alert_handler
