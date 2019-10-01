// Generated register defines for PINMUX

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _PINMUX_REG_DEFS_
#define _PINMUX_REG_DEFS_

// Register write enable for all control registers.
#define PINMUX_REGEN(id) (PINMUX##id##_BASE_ADDR + 0x0)
#define PINMUX_REGEN 0

// Mux select for peripheral inputs.
#define PINMUX_PERIPH_INSEL(id) (PINMUX##id##_BASE_ADDR + 0x4)
#define PINMUX_PERIPH_INSEL_IN0_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN0_OFFSET 0
#define PINMUX_PERIPH_INSEL_IN1_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN1_OFFSET 3
#define PINMUX_PERIPH_INSEL_IN2_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN2_OFFSET 6
#define PINMUX_PERIPH_INSEL_IN3_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN3_OFFSET 9
#define PINMUX_PERIPH_INSEL_IN4_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN4_OFFSET 12
#define PINMUX_PERIPH_INSEL_IN5_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN5_OFFSET 15
#define PINMUX_PERIPH_INSEL_IN6_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN6_OFFSET 18
#define PINMUX_PERIPH_INSEL_IN7_MASK 0x7
#define PINMUX_PERIPH_INSEL_IN7_OFFSET 21

// Mux select for MIO outputs.
#define PINMUX_MIO_OUTSEL(id) (PINMUX##id##_BASE_ADDR + 0x8)
#define PINMUX_MIO_OUTSEL_OUT0_MASK 0xf
#define PINMUX_MIO_OUTSEL_OUT0_OFFSET 0
#define PINMUX_MIO_OUTSEL_OUT1_MASK 0xf
#define PINMUX_MIO_OUTSEL_OUT1_OFFSET 4
#define PINMUX_MIO_OUTSEL_OUT2_MASK 0xf
#define PINMUX_MIO_OUTSEL_OUT2_OFFSET 8
#define PINMUX_MIO_OUTSEL_OUT3_MASK 0xf
#define PINMUX_MIO_OUTSEL_OUT3_OFFSET 12

#endif  // _PINMUX_REG_DEFS_
// End generated register defines for PINMUX
