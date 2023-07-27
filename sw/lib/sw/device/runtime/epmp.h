// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_EPMP_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_EPMP_H_

#include <stdint.h>

/**
 * Enhanced Physical Memory Protection (EPMP).
 *
 * This library is intended for PMP entry configuration management in Machine
 * mode (M-mode).
 *
 * Assumptions (should be initialized in assembly but can be verified using
 * `epmp_check`):
 *   - Machine Mode Whitelist Policy is enabled (mseccfg.MMWP = 1)
 *   - Machine Mode Lockdown is not set (mseccfg.MML = 0)
 *
 * Typically this library will be used with Rule Locking Bypass
 * (mseccfg.RLB = 1) enabled however this is not a hard requirement and RLB
 * can be disabled using this library.
 *
 * Ibex PMP Documentation:
 * https://ibex-core.readthedocs.io/en/latest/03_reference/pmp.html
 */

/**
 * EPMP entry permissions.
 *
 * Entries configured with locked permissions may only be modified
 * if Rule Locking Bypass is set (mseccfg.RLB = 1).
 *
 * When Machine Mode Lockdown is disabled (mseccfg.MML = 0) the
 * combination R=0 W=1 is reserved. This is the assumed state and so
 * it is not possible to set these values. The combination R=1 W=1
 * X=1 has also been reserved by this library and may not be used.
 *
 * An entry may only be configured with unlocked permissions if the
 * entry is also configured as OFF.
 *
 * Note: permissions may have different meanings when Machine Mode
 * Lockdown (mseccfg.MML) is set.
 */
typedef enum epmp_perm {
  /**
   * Unlocked with R=0, W=0 and X=0.
   *
   * Note: full access (R=1, W=1 and X=1) in Machine Mode. Only use
   * in disabled (OFF) entries.
   */
  kEpmpPermUnlocked,

  /**
   * Locked with R=0, W=0 and X=0.
   */
  kEpmpPermLockedNoAccess,

  /**
   * Locked with R=0, W=0 and X=1.
   */
  kEpmpPermLockedExecuteOnly,

  /**
   * Locked with R=1, W=0 and X=0.
   */
  kEpmpPermLockedReadOnly,

  /**
   * Locked with R=1, W=0 and X=1.
   */
  kEpmpPermLockedReadExecute,

  /**
   * Locked with R=1, W=1 and X=0.
   */
  kEpmpPermLockedReadWrite,
} epmp_perm_t;

/**
 * EPMP constants.
 */
enum {
  kEpmpNumRegions = 16,
};

/**
 * EPMP region specification.
 *
 * Provides the start and end addresses of a particular region. These addresses
 * are byte-aligned (i.e. they are like regular pointers rather than encoded
 * addresses).
 *
 * The `start` address is inclusive and the `end` address is exclusive.
 */
typedef struct epmp_region {
  uintptr_t start;
  uintptr_t end;
} epmp_region_t;

/**
 * EPMP entry index.
 */
typedef enum epmp_entry {
  kEpmpEntry0,
  kEpmpEntry1,
  kEpmpEntry2,
  kEpmpEntry3,
  kEpmpEntry4,
  kEpmpEntry5,
  kEpmpEntry6,
  kEpmpEntry7,
  kEpmpEntry8,
  kEpmpEntry9,
  kEpmpEntry10,
  kEpmpEntry11,
  kEpmpEntry12,
  kEpmpEntry13,
  kEpmpEntry14,
  kEpmpEntry15,
} epmp_entry_t;

/**
 * EPMP entry count.
 */
typedef enum epmp_entry_count {
  kEpmpEntryCount0,
  kEpmpEntryCount1,
  kEpmpEntryCount2,
  kEpmpEntryCount3,
  kEpmpEntryCount4,
  kEpmpEntryCount5,
  kEpmpEntryCount6,
  kEpmpEntryCount7,
  kEpmpEntryCount8,
  kEpmpEntryCount9,
  kEpmpEntryCount10,
  kEpmpEntryCount11,
  kEpmpEntryCount12,
  kEpmpEntryCount13,
  kEpmpEntryCount14,
  kEpmpEntryCount15,
  kEpmpEntryCount16,
} epmp_entry_count_t;

/**
 * EPMP generic status codes.
 *
 * These error codes can be used by any function. However if a function
 * requires additional status codes, it must define a set of status codes to
 * be used exclusively by such function.
 */
typedef enum epmp_result {
  kEpmpOk = 0,
  kEpmpError,
  kEpmpBadArg,
} epmp_result_t;

/**
 * Initialize the EPMP library.
 *
 * The current state of the EPMP CSRs will be read and stored inside the
 * library. This function must be called before using the library. The
 * library can only be initialized once.
 *
 * Note: it may be desirable to check the state is as expected. This
 * can be done using `epmp_get_state`.
 */
epmp_result_t epmp_init(void);

/**
 * Check that the actual EPMP state matches what the library expects
 * it to be.
 */
epmp_result_t epmp_check(void);

/**
 * Start an EPMP transaction.
 *
 * A new transaction will be initialized to expect the given number of
 * entries to be reconfigured. Only one transaction may be in progress
 * at a time. Each entry may only be reconfigured once per transaction.
 * Call `epmp_transaction_end` to finalize the transaction and update
 * the EPMP control registers.
 *
 * @param count Number of entries to be configured.
 * @returns `epmp_result_t`
 */
epmp_result_t epmp_transaction_start(epmp_entry_count_t count);

/**
 * Finish an EPMP transaction and update EPMP control registers.
 *
 * Check that the expected number of regions have been reconfigured and
 * then update the EPMP control registers. Once this call returns the
 * transaction will be complete and a new transaction should be
 * started if further updates are required.
 *
 * This call will also perform checks equivalent to an `epmp_check`
 * call before modifying any registers.
 *
 * Updates will occur in the following sequence:
 *
 *   1. pmpaddr0-pmpaddr15
 *   2. pmpcfg0-pmpcfg3
 *
 * @param count Number of entries that should have been configured.
 * @returns `epmp_result_t`
 */
epmp_result_t epmp_transaction_end(epmp_entry_count_t count);

/**
 * EPMP configuration status codes.
 */
typedef enum epmp_entry_configure_result {
  kEpmpEntryConfigureOk = kEpmpOk,
  kEpmpEntryConfigureError = kEpmpError,
  kEpmpEntryConfigureBadArg = kEpmpBadArg,

  /**
   * Invalid addresses provided for the selected address mode.
   */
  kEpmpEntryConfigureBadRegion,

  /**
   * The transaction is in a bad state. This can be caused by:
   *  - Missing call the `epmp_transaction_start`.
   *  - An attempt to configure more entries than was initially specified.
   *  - A prior configuration attempt encountered an error.
   */
  kEpmpEntryConfigureBadTransaction,

  /**
   * The requested entry is out of range or has previously been configured
   * in this transaction. Each entry may only be configured once per
   * transaction.
   */
  kEpmpEntryConfigureBadEntry,

  /**
   * Encoding the entry would interfere with a different pre-existing entry.
   *
   * New entries will be rejected if they:
   *  - Modify the start or end address of an adjacent TOR entry.
   *  - Would result in an address being used in both a NAPOT/NA4 entry and a
   *    TOR entry.
   */
  kEpmpEntryConfigureConflict,
} epmp_entry_configure_result_t;

/**
 * Disable address matching for a PMP entry.
 *
 * The `region` start address will be encoded and configured as the address
 * register for `entry`. The length of `region` must be 0 (i.e. the `region` end
 * address must match the start address). If the following entry is configured
 * using the TOR address mode then the `region` start address must match the
 * pre-existing address.
 *
 * Note: addresses are encoded by dividing them by four. This matches the
 * address encoding used by the TOR address mode.
 *
 * IMPORTANT: the `pmpaddr` and `pmpcfg` control registers will not be
 * updated until `epmp_transaction_end` is called.
 *
 * Example:
 *
 *   ...
 *   res0 = epmp_transaction_start(kEpmpEntryCount2);
 *   res1 = epmp_entry_configure_off(kEpmpEntry0,
 *              (epmp_region_t){0},
 *              kEpmpPermUnlocked);
 *   res2 = epmp_entry_configure_off(kEpmpEntry1,
 *              (epmp_region_t){ .start = 0x10, .end = 0x10 },
 *              kEpmpPermLockedNoAccess);
 *   res3 = epmp_transaction_end(kEpmpEntryCount2);
 *   ...
 *
 * Result:
 *
 *   Entry | Value of `pmpaddr` | Value of `pmpcfg` |
 *   ======+====================+===================+
 *       0 |   0x00 (0x00 >> 2) |         0b0000000 |
 *       1 |   0x04 (0x10 >> 2) |         0b1000000 |
 *
 * @param entry Entry index to update (0 <= `entry` < `kEpmpNumRegions`)
 * @param region Region to encode into `pmpaddr`.
 * @param permissions Updated permissions to write to pmpcfg for `entry`.
 * @return `epmp_entry_configure_result_t`.
 */
epmp_entry_configure_result_t epmp_entry_configure_off(epmp_entry_t entry,
                                                       epmp_region_t region,
                                                       epmp_perm_t permissions);

/**
 * Configures a PMP entry using the Top Of Range (TOR) address mode.
 *
 * The `region` end address will be encoded and configured as the address
 * register associated with `entry`.
 *
 * The `region` start address will be encoded and configured as the address
 * register associated with the preceding entry if that entry is disabled (i.e.
 * configured as OFF). If the preceding entry is configured using TOR mode then
 * its pre-configured end address must match the `region` start address. This
 * behavior allows adjacent regions configured using TOR to share an address,
 * removing the need for a disabled entry between them. If configuring entry 0
 * then the `region` start address must be 0. All other configurations will be
 * rejected.
 *
 * IMPORTANT: the `pmpaddr` and `pmpcfg` control registers will not be
 * updated until `epmp_transaction_end` is called.
 *
 * Example (two adjacent TOR regions + one standalone TOR region):
 *
 *   ...
 *   res0 = epmp_transaction_start(kEpmpEntryCount4);
 *   res1 = epmp_entry_configure_tor(kEpmpEntry0,
 *              (epmp_region_t){ .start = 0x00, .end = 0x10 },
 *              kEpmpPermLockedReadOnly);
 *   res2 = epmp_entry_configure_tor(kEpmpEntry1,
 *              (epmp_region_t){ .start = 0x10, .end = 0x20 },
 *              kEpmpPermLockedReadOnly);
 *   res3 = epmp_entry_configure_off(kEpmpEntry2,
 *              (epmp_region_t){ .start = 0x00, .end = 0x00 },
 *              kEpmpPermLockedNoAccess);
 *   res4 = epmp_entry_configure_tor(kEpmpEntry3,
 *              (epmp_region_t){ .start = 0x30, .end = 0x40 },
 *              kEpmpPermLockedReadOnly);
 *   res5 = epmp_transaction_end(kEpmpEntryCount4);
 *   ...
 *
 * Result:
 *
 *   Entry | Value of `pmpaddr` | Value of `pmpcfg` |
 *   ======+====================+===================+
 *       0 |   0x04 (0x10 >> 2) |         0b1001001 |
 *       1 |   0x08 (0x20 >> 2) |         0b1001001 |
 *       2 |   0x0c (0x30 >> 2) |         0b1000000 |
 *       3 |   0x10 (0x40 >> 2) |         0b1001001 |
 *
 * @param entry Entry index to update (0 <= `entry` < `kEpmpNumRegions`)
 * @param region Region start and end addresses. Start address must be 0
 *        for `entry` 0.
 * @param permissions Updated permissions to write to pmpcfg for `entry`.
 * @return `epmp_entry_configure_result_t`.
 */
epmp_entry_configure_result_t epmp_entry_configure_tor(epmp_entry_t entry,
                                                       epmp_region_t region,
                                                       epmp_perm_t permissions);

/**
 * Configures a PMP entry using the Naturally Aligned 4-byte (NA4) address mode.
 *
 * The `region` start address will be encoded and configured as the address in
 * `entry`. The length of `region` must be exactly four bytes.
 *
 * This function will return `kEpmpEntryConfigureBadRegion` if
 * the PMP granularity is greater than 0.
 *
 * IMPORTANT: the `pmpaddr` and `pmpcfg` control registers will not be
 * updated until `epmp_transaction_end` is called.
 *
 * Example:
 *
 *   ...
 *   res0 = epmp_transaction_start(kEpmpEntryCount1);
 *   res1 = epmp_entry_configure_na4(kEpmpEntry0,
 *              (epmp_region_t){ .start = 0x10, .end = 0x14 },
 *              kEpmpPermLockedReadOnly);
 *   res2 = epmp_transaction_end(kEpmpEntryCount1);
 *   ...
 *
 * Result:
 *
 *   Entry | Value of `pmpaddr` | Value of `pmpcfg` |
 *   ======+====================+===================+
 *       0 |   0x04 (0x10 >> 2) |         0b1010001 |
 *
 * @param entry Entry index to update (0 <= `entry` < `kEpmpNumRegions`)
 * @param region Region start and end addresses. Must be 4 byte aligned.
 * @param permissions Updated permissions to write to pmpcfg for `entry`.
 * @return `epmp_entry_configure_result_t`.
 */
epmp_entry_configure_result_t epmp_entry_configure_na4(epmp_entry_t entry,
                                                       epmp_region_t region,
                                                       epmp_perm_t permissions);

/**
 * Configures a PMP entry using the Naturally Aligned Power-Of-Two (NAPOT)
 * address mode.
 *
 * The `region` will be encoded and configured as the address for `entry`.
 * The length of `region` must be a power of two greater than four and the
 * `region` (both start and end addresses) must also be aligned to the same
 * power of two.
 *
 * If the PMP granularity (G) is greater than zero then the entire `region`
 * must also be aligned to `2 ** (2 + G)`.
 *
 * IMPORTANT: the `pmpaddr` and `pmpcfg` control registers will not be
 * updated until `epmp_transaction_end` is called.
 *
 * Example:
 *
 *   ...
 *   res0 = epmp_transaction_start(kEpmpEntryCount2);
 *   res1 = epmp_entry_configure_napot(kEpmpEntry0,
 *              (epmp_region_t){ .start = 0x10, .end = 0x20 },
 *              kEpmpPermLockedReadOnly);
 *   res2 = epmp_entry_configure_napot(kEpmpEntry1,
 *              (epmp_region_t){ .start = 0x50, .end = 0x58 },
 *              kEpmpPermLockedReadWrite);
 *   res3 = epmp_transaction_end(kEpmpEntryCount2);
 *   ...
 *
 * Result:
 *
 *   Entry | Value of `pmpaddr`        | Value of `pmpcfg` |
 *   ======+===========================+===================+
 *       0 | 0x41 ((0x10 >> 2) | 0b01) |         0b1011001 |
 *       1 | 0x14 ((0x50 >> 2) | 0b00) |         0b1011011 |
 *
 * @param entry Entry index to update (0 <= `entry` < `kEpmpNumRegions`)
 * @param region Region start and end addresses.
 * @param permissions Updated permissions to write to pmpcfg for `entry`.
 * @return `epmp_entry_configure_result_t`.
 */
epmp_entry_configure_result_t epmp_entry_configure_napot(
    epmp_entry_t entry, epmp_region_t region, epmp_perm_t permissions);

/**
 * Disable the Rule Locking Bypass (RLB) feature.
 *
 * When enabled (mseccfg.RLB = 1) the Rule Locking Bypass features allows
 * locked entries to be modified. If any PMP entries are locked and RLB
 * is disabled (mseccfg.RLB = 0) then it is no longer possible to enable
 * RLB. RLB will disabled or an error will be returned.
 *
 * @return `epmp_result_t`
 */
epmp_result_t epmp_disable_rule_locking_bypass(void);

/**
 * A copy of EPMP control register state for debugging purposes.
 */
typedef struct epmp_debug_state {
  /**
   * PMP configuration values (pmp0cfg - pmp15cfg).
   *
   * These configuration values are stored in registers pmpcfg0 - pmpcfg3.
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
  uint8_t pmpcfg[kEpmpNumRegions];

  /**
   * PMP address registers (pmpaddr0 - pmpaddr15).
   *
   * The way that address register values are interpreted differs
   * depending on the address-matching mode (A) in the relevant pmpcfg
   * register(s).
   */
  uintptr_t pmpaddr[kEpmpNumRegions];

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
   */
  uint64_t mseccfg;
} epmp_debug_state_t;

/**
 * Get the current PMP configuration.
 *
 * Read all the PMP CSRs and return their values.
 *
 * @param[out] state Destination to write register values to.
 * @return `epmp_result_t`
 */
epmp_result_t epmp_debug_get_state(epmp_debug_state_t *state);

/**
 * Read the current staged register state.
 *
 * The staged state consists of values that have been configured as
 * part of an ongoing transaction. It therefore only makes sense to call
 * this function after `epmp_transaction_start` and before
 * `epmp_transaction_end`.
 *
 * @param[out] state Destination to write register values to.
 * @return `epmp_result_t`
 */
epmp_result_t epmp_debug_get_transaction_state(epmp_debug_state_t *state);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_EPMP_H_
