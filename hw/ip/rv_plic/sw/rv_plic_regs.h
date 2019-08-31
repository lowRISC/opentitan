// Generated register defines for RV_PLIC

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _RV_PLIC_REG_DEFS_
#define _RV_PLIC_REG_DEFS_

// Interrupt Pending
#define RV_PLIC_IP(id) (RV_PLIC##id##_BASE_ADDR + 0x0)
#define RV_PLIC_IP_P0 0
#define RV_PLIC_IP_P1 1
#define RV_PLIC_IP_P2 2
#define RV_PLIC_IP_P3 3
#define RV_PLIC_IP_P4 4
#define RV_PLIC_IP_P5 5
#define RV_PLIC_IP_P6 6
#define RV_PLIC_IP_P7 7
#define RV_PLIC_IP_P8 8
#define RV_PLIC_IP_P9 9
#define RV_PLIC_IP_P10 10
#define RV_PLIC_IP_P11 11
#define RV_PLIC_IP_P12 12
#define RV_PLIC_IP_P13 13
#define RV_PLIC_IP_P14 14
#define RV_PLIC_IP_P15 15
#define RV_PLIC_IP_P16 16
#define RV_PLIC_IP_P17 17
#define RV_PLIC_IP_P18 18
#define RV_PLIC_IP_P19 19
#define RV_PLIC_IP_P20 20
#define RV_PLIC_IP_P21 21
#define RV_PLIC_IP_P22 22
#define RV_PLIC_IP_P23 23
#define RV_PLIC_IP_P24 24
#define RV_PLIC_IP_P25 25
#define RV_PLIC_IP_P26 26
#define RV_PLIC_IP_P27 27
#define RV_PLIC_IP_P28 28
#define RV_PLIC_IP_P29 29
#define RV_PLIC_IP_P30 30
#define RV_PLIC_IP_P31 31

// Interrupt Source mode. 0: Level, 1: Edge-triggered
#define RV_PLIC_LE(id) (RV_PLIC##id##_BASE_ADDR + 0x4)
#define RV_PLIC_LE_LE0 0
#define RV_PLIC_LE_LE1 1
#define RV_PLIC_LE_LE2 2
#define RV_PLIC_LE_LE3 3
#define RV_PLIC_LE_LE4 4
#define RV_PLIC_LE_LE5 5
#define RV_PLIC_LE_LE6 6
#define RV_PLIC_LE_LE7 7
#define RV_PLIC_LE_LE8 8
#define RV_PLIC_LE_LE9 9
#define RV_PLIC_LE_LE10 10
#define RV_PLIC_LE_LE11 11
#define RV_PLIC_LE_LE12 12
#define RV_PLIC_LE_LE13 13
#define RV_PLIC_LE_LE14 14
#define RV_PLIC_LE_LE15 15
#define RV_PLIC_LE_LE16 16
#define RV_PLIC_LE_LE17 17
#define RV_PLIC_LE_LE18 18
#define RV_PLIC_LE_LE19 19
#define RV_PLIC_LE_LE20 20
#define RV_PLIC_LE_LE21 21
#define RV_PLIC_LE_LE22 22
#define RV_PLIC_LE_LE23 23
#define RV_PLIC_LE_LE24 24
#define RV_PLIC_LE_LE25 25
#define RV_PLIC_LE_LE26 26
#define RV_PLIC_LE_LE27 27
#define RV_PLIC_LE_LE28 28
#define RV_PLIC_LE_LE29 29
#define RV_PLIC_LE_LE30 30
#define RV_PLIC_LE_LE31 31

// Interrupt Source 0 Priority
#define RV_PLIC_PRIO0(id) (RV_PLIC##id##_BASE_ADDR + 0x8)
#define RV_PLIC_PRIO0_MASK 0x7
#define RV_PLIC_PRIO0_OFFSET 0

// Interrupt Source 1 Priority
#define RV_PLIC_PRIO1(id) (RV_PLIC##id##_BASE_ADDR + 0xc)
#define RV_PLIC_PRIO1_MASK 0x7
#define RV_PLIC_PRIO1_OFFSET 0

// Interrupt Source 2 Priority
#define RV_PLIC_PRIO2(id) (RV_PLIC##id##_BASE_ADDR + 0x10)
#define RV_PLIC_PRIO2_MASK 0x7
#define RV_PLIC_PRIO2_OFFSET 0

// Interrupt Source 3 Priority
#define RV_PLIC_PRIO3(id) (RV_PLIC##id##_BASE_ADDR + 0x14)
#define RV_PLIC_PRIO3_MASK 0x7
#define RV_PLIC_PRIO3_OFFSET 0

// Interrupt Source 4 Priority
#define RV_PLIC_PRIO4(id) (RV_PLIC##id##_BASE_ADDR + 0x18)
#define RV_PLIC_PRIO4_MASK 0x7
#define RV_PLIC_PRIO4_OFFSET 0

// Interrupt Source 5 Priority
#define RV_PLIC_PRIO5(id) (RV_PLIC##id##_BASE_ADDR + 0x1c)
#define RV_PLIC_PRIO5_MASK 0x7
#define RV_PLIC_PRIO5_OFFSET 0

// Interrupt Source 6 Priority
#define RV_PLIC_PRIO6(id) (RV_PLIC##id##_BASE_ADDR + 0x20)
#define RV_PLIC_PRIO6_MASK 0x7
#define RV_PLIC_PRIO6_OFFSET 0

// Interrupt Source 7 Priority
#define RV_PLIC_PRIO7(id) (RV_PLIC##id##_BASE_ADDR + 0x24)
#define RV_PLIC_PRIO7_MASK 0x7
#define RV_PLIC_PRIO7_OFFSET 0

// Interrupt Source 8 Priority
#define RV_PLIC_PRIO8(id) (RV_PLIC##id##_BASE_ADDR + 0x28)
#define RV_PLIC_PRIO8_MASK 0x7
#define RV_PLIC_PRIO8_OFFSET 0

// Interrupt Source 9 Priority
#define RV_PLIC_PRIO9(id) (RV_PLIC##id##_BASE_ADDR + 0x2c)
#define RV_PLIC_PRIO9_MASK 0x7
#define RV_PLIC_PRIO9_OFFSET 0

// Interrupt Source 10 Priority
#define RV_PLIC_PRIO10(id) (RV_PLIC##id##_BASE_ADDR + 0x30)
#define RV_PLIC_PRIO10_MASK 0x7
#define RV_PLIC_PRIO10_OFFSET 0

// Interrupt Source 11 Priority
#define RV_PLIC_PRIO11(id) (RV_PLIC##id##_BASE_ADDR + 0x34)
#define RV_PLIC_PRIO11_MASK 0x7
#define RV_PLIC_PRIO11_OFFSET 0

// Interrupt Source 12 Priority
#define RV_PLIC_PRIO12(id) (RV_PLIC##id##_BASE_ADDR + 0x38)
#define RV_PLIC_PRIO12_MASK 0x7
#define RV_PLIC_PRIO12_OFFSET 0

// Interrupt Source 13 Priority
#define RV_PLIC_PRIO13(id) (RV_PLIC##id##_BASE_ADDR + 0x3c)
#define RV_PLIC_PRIO13_MASK 0x7
#define RV_PLIC_PRIO13_OFFSET 0

// Interrupt Source 14 Priority
#define RV_PLIC_PRIO14(id) (RV_PLIC##id##_BASE_ADDR + 0x40)
#define RV_PLIC_PRIO14_MASK 0x7
#define RV_PLIC_PRIO14_OFFSET 0

// Interrupt Source 15 Priority
#define RV_PLIC_PRIO15(id) (RV_PLIC##id##_BASE_ADDR + 0x44)
#define RV_PLIC_PRIO15_MASK 0x7
#define RV_PLIC_PRIO15_OFFSET 0

// Interrupt Source 16 Priority
#define RV_PLIC_PRIO16(id) (RV_PLIC##id##_BASE_ADDR + 0x48)
#define RV_PLIC_PRIO16_MASK 0x7
#define RV_PLIC_PRIO16_OFFSET 0

// Interrupt Source 17 Priority
#define RV_PLIC_PRIO17(id) (RV_PLIC##id##_BASE_ADDR + 0x4c)
#define RV_PLIC_PRIO17_MASK 0x7
#define RV_PLIC_PRIO17_OFFSET 0

// Interrupt Source 18 Priority
#define RV_PLIC_PRIO18(id) (RV_PLIC##id##_BASE_ADDR + 0x50)
#define RV_PLIC_PRIO18_MASK 0x7
#define RV_PLIC_PRIO18_OFFSET 0

// Interrupt Source 19 Priority
#define RV_PLIC_PRIO19(id) (RV_PLIC##id##_BASE_ADDR + 0x54)
#define RV_PLIC_PRIO19_MASK 0x7
#define RV_PLIC_PRIO19_OFFSET 0

// Interrupt Source 20 Priority
#define RV_PLIC_PRIO20(id) (RV_PLIC##id##_BASE_ADDR + 0x58)
#define RV_PLIC_PRIO20_MASK 0x7
#define RV_PLIC_PRIO20_OFFSET 0

// Interrupt Source 21 Priority
#define RV_PLIC_PRIO21(id) (RV_PLIC##id##_BASE_ADDR + 0x5c)
#define RV_PLIC_PRIO21_MASK 0x7
#define RV_PLIC_PRIO21_OFFSET 0

// Interrupt Source 22 Priority
#define RV_PLIC_PRIO22(id) (RV_PLIC##id##_BASE_ADDR + 0x60)
#define RV_PLIC_PRIO22_MASK 0x7
#define RV_PLIC_PRIO22_OFFSET 0

// Interrupt Source 23 Priority
#define RV_PLIC_PRIO23(id) (RV_PLIC##id##_BASE_ADDR + 0x64)
#define RV_PLIC_PRIO23_MASK 0x7
#define RV_PLIC_PRIO23_OFFSET 0

// Interrupt Source 24 Priority
#define RV_PLIC_PRIO24(id) (RV_PLIC##id##_BASE_ADDR + 0x68)
#define RV_PLIC_PRIO24_MASK 0x7
#define RV_PLIC_PRIO24_OFFSET 0

// Interrupt Source 25 Priority
#define RV_PLIC_PRIO25(id) (RV_PLIC##id##_BASE_ADDR + 0x6c)
#define RV_PLIC_PRIO25_MASK 0x7
#define RV_PLIC_PRIO25_OFFSET 0

// Interrupt Source 26 Priority
#define RV_PLIC_PRIO26(id) (RV_PLIC##id##_BASE_ADDR + 0x70)
#define RV_PLIC_PRIO26_MASK 0x7
#define RV_PLIC_PRIO26_OFFSET 0

// Interrupt Source 27 Priority
#define RV_PLIC_PRIO27(id) (RV_PLIC##id##_BASE_ADDR + 0x74)
#define RV_PLIC_PRIO27_MASK 0x7
#define RV_PLIC_PRIO27_OFFSET 0

// Interrupt Source 28 Priority
#define RV_PLIC_PRIO28(id) (RV_PLIC##id##_BASE_ADDR + 0x78)
#define RV_PLIC_PRIO28_MASK 0x7
#define RV_PLIC_PRIO28_OFFSET 0

// Interrupt Source 29 Priority
#define RV_PLIC_PRIO29(id) (RV_PLIC##id##_BASE_ADDR + 0x7c)
#define RV_PLIC_PRIO29_MASK 0x7
#define RV_PLIC_PRIO29_OFFSET 0

// Interrupt Source 30 Priority
#define RV_PLIC_PRIO30(id) (RV_PLIC##id##_BASE_ADDR + 0x80)
#define RV_PLIC_PRIO30_MASK 0x7
#define RV_PLIC_PRIO30_OFFSET 0

// Interrupt Source 31 Priority
#define RV_PLIC_PRIO31(id) (RV_PLIC##id##_BASE_ADDR + 0x84)
#define RV_PLIC_PRIO31_MASK 0x7
#define RV_PLIC_PRIO31_OFFSET 0

// Interrupt Enable for Target 0
#define RV_PLIC_IE0(id) (RV_PLIC##id##_BASE_ADDR + 0x100)
#define RV_PLIC_IE0_E0 0
#define RV_PLIC_IE0_E1 1
#define RV_PLIC_IE0_E2 2
#define RV_PLIC_IE0_E3 3
#define RV_PLIC_IE0_E4 4
#define RV_PLIC_IE0_E5 5
#define RV_PLIC_IE0_E6 6
#define RV_PLIC_IE0_E7 7
#define RV_PLIC_IE0_E8 8
#define RV_PLIC_IE0_E9 9
#define RV_PLIC_IE0_E10 10
#define RV_PLIC_IE0_E11 11
#define RV_PLIC_IE0_E12 12
#define RV_PLIC_IE0_E13 13
#define RV_PLIC_IE0_E14 14
#define RV_PLIC_IE0_E15 15
#define RV_PLIC_IE0_E16 16
#define RV_PLIC_IE0_E17 17
#define RV_PLIC_IE0_E18 18
#define RV_PLIC_IE0_E19 19
#define RV_PLIC_IE0_E20 20
#define RV_PLIC_IE0_E21 21
#define RV_PLIC_IE0_E22 22
#define RV_PLIC_IE0_E23 23
#define RV_PLIC_IE0_E24 24
#define RV_PLIC_IE0_E25 25
#define RV_PLIC_IE0_E26 26
#define RV_PLIC_IE0_E27 27
#define RV_PLIC_IE0_E28 28
#define RV_PLIC_IE0_E29 29
#define RV_PLIC_IE0_E30 30
#define RV_PLIC_IE0_E31 31

// Threshold of priority for Target 0
#define RV_PLIC_THRESHOLD0(id) (RV_PLIC##id##_BASE_ADDR + 0x104)
#define RV_PLIC_THRESHOLD0_MASK 0x7
#define RV_PLIC_THRESHOLD0_OFFSET 0

// Claim by read, complete by write for Target 0
#define RV_PLIC_CC0(id) (RV_PLIC##id##_BASE_ADDR + 0x108)
#define RV_PLIC_CC0_MASK 0x3f
#define RV_PLIC_CC0_OFFSET 0

// msip for Hart 0. Write 1 to here asserts msip_o[0]
#define RV_PLIC_MSIP0(id) (RV_PLIC##id##_BASE_ADDR + 0x10c)
#define RV_PLIC_MSIP0 0

#endif  // _RV_PLIC_REG_DEFS_
// End generated register defines for RV_PLIC
