// Generated register defines for pwm

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _PWM_REG_DEFS_
#define _PWM_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Number of PWM outputs
#define PWM_PARAM_N_OUTPUTS 6

// Number of alerts
#define PWM_PARAM_NUM_ALERTS 1

// Register width
#define PWM_PARAM_REG_WIDTH 32

// Alert Test Register
#define PWM_ALERT_TEST_REG_OFFSET 0x0
#define PWM_ALERT_TEST_REG_RESVAL 0x0
#define PWM_ALERT_TEST_FATAL_FAULT_BIT 0

// Register write enable for all control registers
#define PWM_REGWEN_REG_OFFSET 0x4
#define PWM_REGWEN_REG_RESVAL 0x1
#define PWM_REGWEN_REGWEN_BIT 0

// Configuration register
#define PWM_CFG_REG_OFFSET 0x8
#define PWM_CFG_REG_RESVAL 0x38008000
#define PWM_CFG_CLK_DIV_MASK 0x7ffffff
#define PWM_CFG_CLK_DIV_OFFSET 0
#define PWM_CFG_CLK_DIV_FIELD \
  ((bitfield_field32_t) { .mask = PWM_CFG_CLK_DIV_MASK, .index = PWM_CFG_CLK_DIV_OFFSET })
#define PWM_CFG_DC_RESN_MASK 0xf
#define PWM_CFG_DC_RESN_OFFSET 27
#define PWM_CFG_DC_RESN_FIELD \
  ((bitfield_field32_t) { .mask = PWM_CFG_DC_RESN_MASK, .index = PWM_CFG_DC_RESN_OFFSET })
#define PWM_CFG_CNTR_EN_BIT 31

// Enable PWM operation for each channel (common parameters)
#define PWM_PWM_EN_EN_FIELD_WIDTH 1
#define PWM_PWM_EN_MULTIREG_COUNT 1

// Enable PWM operation for each channel
#define PWM_PWM_EN_REG_OFFSET 0xc
#define PWM_PWM_EN_REG_RESVAL 0x0
#define PWM_PWM_EN_EN_0_BIT 0
#define PWM_PWM_EN_EN_1_BIT 1
#define PWM_PWM_EN_EN_2_BIT 2
#define PWM_PWM_EN_EN_3_BIT 3
#define PWM_PWM_EN_EN_4_BIT 4
#define PWM_PWM_EN_EN_5_BIT 5

// Invert the PWM output for each channel (common parameters)
#define PWM_INVERT_INVERT_FIELD_WIDTH 1
#define PWM_INVERT_MULTIREG_COUNT 1

// Invert the PWM output for each channel
#define PWM_INVERT_REG_OFFSET 0x10
#define PWM_INVERT_REG_RESVAL 0x0
#define PWM_INVERT_INVERT_0_BIT 0
#define PWM_INVERT_INVERT_1_BIT 1
#define PWM_INVERT_INVERT_2_BIT 2
#define PWM_INVERT_INVERT_3_BIT 3
#define PWM_INVERT_INVERT_4_BIT 4
#define PWM_INVERT_INVERT_5_BIT 5

// Basic PWM Channel Parameters (common parameters)
#define PWM_PWM_PARAM_PHASE_DELAY_FIELD_WIDTH 16
#define PWM_PWM_PARAM_HTBT_EN_FIELD_WIDTH 1
#define PWM_PWM_PARAM_BLINK_EN_FIELD_WIDTH 1
#define PWM_PWM_PARAM_MULTIREG_COUNT 6

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_0_REG_OFFSET 0x14
#define PWM_PWM_PARAM_0_REG_RESVAL 0x0
#define PWM_PWM_PARAM_0_PHASE_DELAY_0_MASK 0xffff
#define PWM_PWM_PARAM_0_PHASE_DELAY_0_OFFSET 0
#define PWM_PWM_PARAM_0_PHASE_DELAY_0_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_0_PHASE_DELAY_0_MASK, .index = PWM_PWM_PARAM_0_PHASE_DELAY_0_OFFSET })
#define PWM_PWM_PARAM_0_HTBT_EN_0_BIT 30
#define PWM_PWM_PARAM_0_BLINK_EN_0_BIT 31

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_1_REG_OFFSET 0x18
#define PWM_PWM_PARAM_1_REG_RESVAL 0x0
#define PWM_PWM_PARAM_1_PHASE_DELAY_1_MASK 0xffff
#define PWM_PWM_PARAM_1_PHASE_DELAY_1_OFFSET 0
#define PWM_PWM_PARAM_1_PHASE_DELAY_1_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_1_PHASE_DELAY_1_MASK, .index = PWM_PWM_PARAM_1_PHASE_DELAY_1_OFFSET })
#define PWM_PWM_PARAM_1_HTBT_EN_1_BIT 30
#define PWM_PWM_PARAM_1_BLINK_EN_1_BIT 31

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_2_REG_OFFSET 0x1c
#define PWM_PWM_PARAM_2_REG_RESVAL 0x0
#define PWM_PWM_PARAM_2_PHASE_DELAY_2_MASK 0xffff
#define PWM_PWM_PARAM_2_PHASE_DELAY_2_OFFSET 0
#define PWM_PWM_PARAM_2_PHASE_DELAY_2_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_2_PHASE_DELAY_2_MASK, .index = PWM_PWM_PARAM_2_PHASE_DELAY_2_OFFSET })
#define PWM_PWM_PARAM_2_HTBT_EN_2_BIT 30
#define PWM_PWM_PARAM_2_BLINK_EN_2_BIT 31

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_3_REG_OFFSET 0x20
#define PWM_PWM_PARAM_3_REG_RESVAL 0x0
#define PWM_PWM_PARAM_3_PHASE_DELAY_3_MASK 0xffff
#define PWM_PWM_PARAM_3_PHASE_DELAY_3_OFFSET 0
#define PWM_PWM_PARAM_3_PHASE_DELAY_3_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_3_PHASE_DELAY_3_MASK, .index = PWM_PWM_PARAM_3_PHASE_DELAY_3_OFFSET })
#define PWM_PWM_PARAM_3_HTBT_EN_3_BIT 30
#define PWM_PWM_PARAM_3_BLINK_EN_3_BIT 31

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_4_REG_OFFSET 0x24
#define PWM_PWM_PARAM_4_REG_RESVAL 0x0
#define PWM_PWM_PARAM_4_PHASE_DELAY_4_MASK 0xffff
#define PWM_PWM_PARAM_4_PHASE_DELAY_4_OFFSET 0
#define PWM_PWM_PARAM_4_PHASE_DELAY_4_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_4_PHASE_DELAY_4_MASK, .index = PWM_PWM_PARAM_4_PHASE_DELAY_4_OFFSET })
#define PWM_PWM_PARAM_4_HTBT_EN_4_BIT 30
#define PWM_PWM_PARAM_4_BLINK_EN_4_BIT 31

// Basic PWM Channel Parameters
#define PWM_PWM_PARAM_5_REG_OFFSET 0x28
#define PWM_PWM_PARAM_5_REG_RESVAL 0x0
#define PWM_PWM_PARAM_5_PHASE_DELAY_5_MASK 0xffff
#define PWM_PWM_PARAM_5_PHASE_DELAY_5_OFFSET 0
#define PWM_PWM_PARAM_5_PHASE_DELAY_5_FIELD \
  ((bitfield_field32_t) { .mask = PWM_PWM_PARAM_5_PHASE_DELAY_5_MASK, .index = PWM_PWM_PARAM_5_PHASE_DELAY_5_OFFSET })
#define PWM_PWM_PARAM_5_HTBT_EN_5_BIT 30
#define PWM_PWM_PARAM_5_BLINK_EN_5_BIT 31

// Controls the duty_cycle of each channel. (common parameters)
#define PWM_DUTY_CYCLE_A_FIELD_WIDTH 16
#define PWM_DUTY_CYCLE_B_FIELD_WIDTH 16
#define PWM_DUTY_CYCLE_MULTIREG_COUNT 6

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_0_REG_OFFSET 0x2c
#define PWM_DUTY_CYCLE_0_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_0_A_0_MASK 0xffff
#define PWM_DUTY_CYCLE_0_A_0_OFFSET 0
#define PWM_DUTY_CYCLE_0_A_0_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_0_A_0_MASK, .index = PWM_DUTY_CYCLE_0_A_0_OFFSET })
#define PWM_DUTY_CYCLE_0_B_0_MASK 0xffff
#define PWM_DUTY_CYCLE_0_B_0_OFFSET 16
#define PWM_DUTY_CYCLE_0_B_0_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_0_B_0_MASK, .index = PWM_DUTY_CYCLE_0_B_0_OFFSET })

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_1_REG_OFFSET 0x30
#define PWM_DUTY_CYCLE_1_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_1_A_1_MASK 0xffff
#define PWM_DUTY_CYCLE_1_A_1_OFFSET 0
#define PWM_DUTY_CYCLE_1_A_1_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_1_A_1_MASK, .index = PWM_DUTY_CYCLE_1_A_1_OFFSET })
#define PWM_DUTY_CYCLE_1_B_1_MASK 0xffff
#define PWM_DUTY_CYCLE_1_B_1_OFFSET 16
#define PWM_DUTY_CYCLE_1_B_1_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_1_B_1_MASK, .index = PWM_DUTY_CYCLE_1_B_1_OFFSET })

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_2_REG_OFFSET 0x34
#define PWM_DUTY_CYCLE_2_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_2_A_2_MASK 0xffff
#define PWM_DUTY_CYCLE_2_A_2_OFFSET 0
#define PWM_DUTY_CYCLE_2_A_2_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_2_A_2_MASK, .index = PWM_DUTY_CYCLE_2_A_2_OFFSET })
#define PWM_DUTY_CYCLE_2_B_2_MASK 0xffff
#define PWM_DUTY_CYCLE_2_B_2_OFFSET 16
#define PWM_DUTY_CYCLE_2_B_2_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_2_B_2_MASK, .index = PWM_DUTY_CYCLE_2_B_2_OFFSET })

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_3_REG_OFFSET 0x38
#define PWM_DUTY_CYCLE_3_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_3_A_3_MASK 0xffff
#define PWM_DUTY_CYCLE_3_A_3_OFFSET 0
#define PWM_DUTY_CYCLE_3_A_3_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_3_A_3_MASK, .index = PWM_DUTY_CYCLE_3_A_3_OFFSET })
#define PWM_DUTY_CYCLE_3_B_3_MASK 0xffff
#define PWM_DUTY_CYCLE_3_B_3_OFFSET 16
#define PWM_DUTY_CYCLE_3_B_3_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_3_B_3_MASK, .index = PWM_DUTY_CYCLE_3_B_3_OFFSET })

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_4_REG_OFFSET 0x3c
#define PWM_DUTY_CYCLE_4_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_4_A_4_MASK 0xffff
#define PWM_DUTY_CYCLE_4_A_4_OFFSET 0
#define PWM_DUTY_CYCLE_4_A_4_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_4_A_4_MASK, .index = PWM_DUTY_CYCLE_4_A_4_OFFSET })
#define PWM_DUTY_CYCLE_4_B_4_MASK 0xffff
#define PWM_DUTY_CYCLE_4_B_4_OFFSET 16
#define PWM_DUTY_CYCLE_4_B_4_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_4_B_4_MASK, .index = PWM_DUTY_CYCLE_4_B_4_OFFSET })

// Controls the duty_cycle of each channel.
#define PWM_DUTY_CYCLE_5_REG_OFFSET 0x40
#define PWM_DUTY_CYCLE_5_REG_RESVAL 0x7fff7fff
#define PWM_DUTY_CYCLE_5_A_5_MASK 0xffff
#define PWM_DUTY_CYCLE_5_A_5_OFFSET 0
#define PWM_DUTY_CYCLE_5_A_5_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_5_A_5_MASK, .index = PWM_DUTY_CYCLE_5_A_5_OFFSET })
#define PWM_DUTY_CYCLE_5_B_5_MASK 0xffff
#define PWM_DUTY_CYCLE_5_B_5_OFFSET 16
#define PWM_DUTY_CYCLE_5_B_5_FIELD \
  ((bitfield_field32_t) { .mask = PWM_DUTY_CYCLE_5_B_5_MASK, .index = PWM_DUTY_CYCLE_5_B_5_OFFSET })

// Hardware controlled blink/heartbeat parameters. (common parameters)
#define PWM_BLINK_PARAM_X_FIELD_WIDTH 16
#define PWM_BLINK_PARAM_Y_FIELD_WIDTH 16
#define PWM_BLINK_PARAM_MULTIREG_COUNT 6

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_0_REG_OFFSET 0x44
#define PWM_BLINK_PARAM_0_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_0_X_0_MASK 0xffff
#define PWM_BLINK_PARAM_0_X_0_OFFSET 0
#define PWM_BLINK_PARAM_0_X_0_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_0_X_0_MASK, .index = PWM_BLINK_PARAM_0_X_0_OFFSET })
#define PWM_BLINK_PARAM_0_Y_0_MASK 0xffff
#define PWM_BLINK_PARAM_0_Y_0_OFFSET 16
#define PWM_BLINK_PARAM_0_Y_0_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_0_Y_0_MASK, .index = PWM_BLINK_PARAM_0_Y_0_OFFSET })

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_1_REG_OFFSET 0x48
#define PWM_BLINK_PARAM_1_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_1_X_1_MASK 0xffff
#define PWM_BLINK_PARAM_1_X_1_OFFSET 0
#define PWM_BLINK_PARAM_1_X_1_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_1_X_1_MASK, .index = PWM_BLINK_PARAM_1_X_1_OFFSET })
#define PWM_BLINK_PARAM_1_Y_1_MASK 0xffff
#define PWM_BLINK_PARAM_1_Y_1_OFFSET 16
#define PWM_BLINK_PARAM_1_Y_1_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_1_Y_1_MASK, .index = PWM_BLINK_PARAM_1_Y_1_OFFSET })

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_2_REG_OFFSET 0x4c
#define PWM_BLINK_PARAM_2_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_2_X_2_MASK 0xffff
#define PWM_BLINK_PARAM_2_X_2_OFFSET 0
#define PWM_BLINK_PARAM_2_X_2_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_2_X_2_MASK, .index = PWM_BLINK_PARAM_2_X_2_OFFSET })
#define PWM_BLINK_PARAM_2_Y_2_MASK 0xffff
#define PWM_BLINK_PARAM_2_Y_2_OFFSET 16
#define PWM_BLINK_PARAM_2_Y_2_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_2_Y_2_MASK, .index = PWM_BLINK_PARAM_2_Y_2_OFFSET })

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_3_REG_OFFSET 0x50
#define PWM_BLINK_PARAM_3_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_3_X_3_MASK 0xffff
#define PWM_BLINK_PARAM_3_X_3_OFFSET 0
#define PWM_BLINK_PARAM_3_X_3_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_3_X_3_MASK, .index = PWM_BLINK_PARAM_3_X_3_OFFSET })
#define PWM_BLINK_PARAM_3_Y_3_MASK 0xffff
#define PWM_BLINK_PARAM_3_Y_3_OFFSET 16
#define PWM_BLINK_PARAM_3_Y_3_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_3_Y_3_MASK, .index = PWM_BLINK_PARAM_3_Y_3_OFFSET })

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_4_REG_OFFSET 0x54
#define PWM_BLINK_PARAM_4_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_4_X_4_MASK 0xffff
#define PWM_BLINK_PARAM_4_X_4_OFFSET 0
#define PWM_BLINK_PARAM_4_X_4_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_4_X_4_MASK, .index = PWM_BLINK_PARAM_4_X_4_OFFSET })
#define PWM_BLINK_PARAM_4_Y_4_MASK 0xffff
#define PWM_BLINK_PARAM_4_Y_4_OFFSET 16
#define PWM_BLINK_PARAM_4_Y_4_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_4_Y_4_MASK, .index = PWM_BLINK_PARAM_4_Y_4_OFFSET })

// Hardware controlled blink/heartbeat parameters.
#define PWM_BLINK_PARAM_5_REG_OFFSET 0x58
#define PWM_BLINK_PARAM_5_REG_RESVAL 0x0
#define PWM_BLINK_PARAM_5_X_5_MASK 0xffff
#define PWM_BLINK_PARAM_5_X_5_OFFSET 0
#define PWM_BLINK_PARAM_5_X_5_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_5_X_5_MASK, .index = PWM_BLINK_PARAM_5_X_5_OFFSET })
#define PWM_BLINK_PARAM_5_Y_5_MASK 0xffff
#define PWM_BLINK_PARAM_5_Y_5_OFFSET 16
#define PWM_BLINK_PARAM_5_Y_5_FIELD \
  ((bitfield_field32_t) { .mask = PWM_BLINK_PARAM_5_Y_5_MASK, .index = PWM_BLINK_PARAM_5_Y_5_OFFSET })

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _PWM_REG_DEFS_
// End generated register defines for pwm