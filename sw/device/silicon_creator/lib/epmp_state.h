// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_STATE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_STATE_H_

#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/epmp_defs.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Silicon creator ePMP library.
 *
 * This library provides functions to create and manage an in-memory copy of the
 * ePMP configuration. To update the hardware configuration please use either
 * assembly or the CSR library directly as needed.
 */

enum {
  /**
   * The number of PMP entries supported by the hardware.
   */
  kEpmpNumRegions = 16,
};

/**
 * PMP configuration permission settings.
 *
 * May be combined with `epmp_mode_t` values to form complete configurations.
 *
 *   Bit | Index
 *   ----+------
 *    L  |  7
 *    R  |  0
 *    W  |  1
 *    X  |  2
 *
 * Combinations not exposed by this enum should not be used. The 'unlocked'
 * zero value should only be used for entries that are configured as OFF.
 */
typedef enum epmp_perm {
  kEpmpPermUnlocked = 0,
  kEpmpPermLockedNoAccess = EPMP_CFG_L,
  kEpmpPermLockedReadOnly = EPMP_CFG_LR,
  kEpmpPermLockedReadWrite = EPMP_CFG_LRW,
  kEpmpPermLockedReadExecute = EPMP_CFG_LRX,
  kEpmpPermLockedReadWriteExecute = EPMP_CFG_LRWX,
} epmp_perm_t;

/**
 * PMP configuration addressing mode fields.
 *
 * May be combined with `epmp_perm_t` values to form complete configurations.
 */
typedef enum epmp_mode {
  kEpmpModeOff = EPMP_CFG_A_OFF,
  kEpmpModeTor = EPMP_CFG_A_TOR,
  kEpmpModeNa4 = EPMP_CFG_A_NA4,
  kEpmpModeNapot = EPMP_CFG_A_NAPOT,
} epmp_mode_t;

/**
 * ePMP region specification.
 *
 * Provides the unencoded start and end addresses of a particular region.
 *
 * The `start` address is inclusive and the `end` address is exclusive.
 */
typedef struct epmp_region {
  uintptr_t start;
  uintptr_t end;
} epmp_region_t;

/**
 * In-memory copy of the ePMP register state.
 */
typedef struct epmp_state {
  /**
   * PMP configuration values (pmpcfg0 - pmpcfg3).
   *
   * The 8-bit configuration values (pmp0cfg - pmp15cfg) are packed into these
   * registers in little-endian byte order.
   *
   * Each 8-bit configuration value is encoded as follows:
   *
   * Layout:
   *
   *   +---+-------+-------+---+---+---+
   *   | L |   0   |   A   | X | W | R |
   *   +---+-------+-------+---+---+---+
   *   8   7   6   5   4   3   2   1   0
   *
   * Key:
   *
   *   L = Locked
   *   A = Address-matching Mode (OFF=0, TOR=1, NA4=2, NAPOT=3)
   *   X = Executable
   *   W = Writeable
   *   R = Readable
   *
   * Note: the interpretation of these configuration bits depends on
   * whether Machine Mode Lockdown (mseccfg.MML) is enabled or not.
   * See the PMP Enhancements specification for more details.
   */
  uint32_t pmpcfg[kEpmpNumRegions / 4];

  /**
   * PMP address registers (pmpaddr0 - pmpaddr15).
   *
   * The way that address register values are interpreted differs
   * depending on the address-matching mode (A) in the relevant pmpcfg
   * register(s).
   */
  uint32_t pmpaddr[kEpmpNumRegions];

  /**
   * Machine Security Configuration register (mseccfg).
   *
   *   +---...---+------+------+------+
   *   |    0    |  RLB | MMWP |  MML |
   *   +---...---+------+------+------+
   *  63         3      2      1     0
   *
   *  Key:
   *
   *    RLB  = Rule Locking Bypass
   *    MMWP = Machine Mode Whitelist Policy
   *    MML  = Machine Mode Lockdown
   *
   * See the PMP Enhancements specification for more details.
   *
   * Note: these are the low 32 bits of mseccfg only. The high 32 bits
   * are set to 0.
   */
  uint32_t mseccfg;
} epmp_state_t;

extern epmp_state_t epmp_state;

/**
 * Configure the given PMP entry in state using the Top-Of-Range addressing
 * mode.
 *
 * @param state The ePMP state to update.
 * @param entry The index of the entry to update.
 * @param region The memory region to encode in the address registers.
 * @param perm The permissions to set for the entry.
 */
inline void epmp_state_configure_tor(uint32_t entry, epmp_region_t region,
                                     epmp_perm_t perm) {
  // Set address registers.
  if (entry > 0) {
    epmp_state.pmpaddr[entry - 1] = region.start >> 2;
  }
  epmp_state.pmpaddr[entry] = region.end >> 2;

  // Set configuration register.
  bitfield_field32_t field = {.mask = 0xff, .index = (entry % 4) * 8};
  epmp_state.pmpcfg[entry / 4] = bitfield_field32_write(
      epmp_state.pmpcfg[entry / 4], field, kEpmpModeTor | perm);
}

/**
 * Configure the given PMP entry in state using the Naturally-Aligned-4-byte
 * addressing mode.
 *
 * @param state The ePMP state to update.
 * @param entry The index of the entry to update.
 * @param region The memory region to encode in the address registers.
 * @param perm The permissions to set for the entry.
 */
inline void epmp_state_configure_na4(uint32_t entry, epmp_region_t region,
                                     epmp_perm_t perm) {
  // Set address register.
  epmp_state.pmpaddr[entry] = region.start >> 2;

  // Set configuration register.
  bitfield_field32_t field = {.mask = 0xff, .index = (entry % 4) * 8};
  epmp_state.pmpcfg[entry / 4] = bitfield_field32_write(
      epmp_state.pmpcfg[entry / 4], field, kEpmpModeNa4 | perm);
}

/**
 * Configure the given PMP entry in state using the
 * Naturally-Aligned-Power-Of-Two addressing mode.
 *
 * @param state The ePMP state to update.
 * @param entry The index of the entry to update.
 * @param region The memory region to encode in the address registers.
 * @param perm The permissions to set for the entry.
 */
inline void epmp_state_configure_napot(uint32_t entry, epmp_region_t region,
                                       epmp_perm_t perm) {
  // Set address register.
  uint32_t len = (region.end - region.start - 1) >> 3;
  epmp_state.pmpaddr[entry] = (region.start >> 2) | len;

  // Set configuration register.
  bitfield_field32_t field = {.mask = 0xff, .index = (entry % 4) * 8};
  epmp_state.pmpcfg[entry / 4] = bitfield_field32_write(
      epmp_state.pmpcfg[entry / 4], field, kEpmpModeNapot | perm);
}

/**
 * Report whether the given state matches the current hardware ePMP
 * configuration.
 *
 * @param state Expected values of the ePMP CSRs.
 * @return Whether the check succeeded.
 */
rom_error_t epmp_state_check(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_EPMP_STATE_H_
