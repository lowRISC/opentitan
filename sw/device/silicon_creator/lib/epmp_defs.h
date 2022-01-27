// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_DEFS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_DEFS_H_

/**
 * Constants for use when interacting with the enhanced Physical Memory
 * Protection control registers.
 *
 * See the Ibex Physical Memory Protection documentation for more
 * details:
 *
 * https://ibex-core.readthedocs.io/en/latest/03_reference/pmp.html
 *
 * Note: this file must be usable from assembly, C and C++ files and
 * should therefore only contain constant definitions.
 */

/**
 * Address of the Machine Security Configuration control register.
 *
 * For use with CSR operations such as read, write, set and clear.
 */
#define EPMP_MSECCFG 0x747

/**
 * Machine Security Configuration bits.
 *
 *   MML = Machine Mode Lockdown
 *   MMWP = Machine Mode Whitelist Policy
 *   RLB = Rule Locking Bypass
 */
#define EPMP_MSECCFG_MML (1 << 0)
#define EPMP_MSECCFG_MMWP (1 << 1)
#define EPMP_MSECCFG_RLB (1 << 2)

/**
 * PMP configuration (`pmpNcfg`) register fields.
 *
 *   8   7       5       3   2   1   0
 *   +---+-------+-------+---+---+---+
 *   | L |   0   |   A   | X | W | R |
 *   +---+-------+-------+---+---+---+
 *
 * Key:
 *
 *   L - lock
 *   A - addressing mode (OFF=0, TOR=1, NA4=2, NAPOT=3)
 *   X - execute
 *   W - write
 *   R - read
 *
 * Note that there are four 8-bit configuration fields (`pmpNcfg`)
 * packed into each hardware configuration register (`pmpcfgN`).
 */
#define EPMP_CFG_L (1 << 7)
#define EPMP_CFG_A_OFF (0 << 3)
#define EPMP_CFG_A_TOR (1 << 3)
#define EPMP_CFG_A_NA4 (2 << 3)
#define EPMP_CFG_A_NAPOT (3 << 3)
#define EPMP_CFG_X (1 << 2)
#define EPMP_CFG_W (1 << 1)
#define EPMP_CFG_R (1 << 0)

/**
 * Common PMP configuration (`pmpNcfg`) permission combinations.
 */
#define EPMP_CFG_LR (EPMP_CFG_L | EPMP_CFG_R)
#define EPMP_CFG_LRX (EPMP_CFG_L | EPMP_CFG_R | EPMP_CFG_X)
#define EPMP_CFG_LRW (EPMP_CFG_L | EPMP_CFG_R | EPMP_CFG_W)
#define EPMP_CFG_LRWX (EPMP_CFG_L | EPMP_CFG_R | EPMP_CFG_W | EPMP_CFG_X)

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_DEFS_H_
