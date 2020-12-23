// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PMP_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PMP_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * RISC-V PMP address matching modes.
 *
 * PMP address matching modes, how protected regions are formed and
 * implementation defined granularity information is described in:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs", "Address Matching".
 *
 * PMP regions matching logic and prioritisation is described in the
 * "Priority and Matching Logic" paragraph of the section "3.6.1".
 *
 * Note that granularity is implementation defined (default G=0, making the
 * minimal PMP region size as 2^(G+2) = 4 bytes), and with G >= 1, the
 * NA4 is not available. Granularity also determines the minimal region size in
 * TOR and NAPOT modes.
 */

/**
 * Attribute for functions which return errors that must be acknowledged.
 *
 * This attribute must be used to mark all PMP API that return an error value of
 * some kind, to ensure that callers do not accidentally drop the error on the
 * ground.
 */
#define PMP_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

/**
 * RV32 PMP CSR definitions.
 *
 * The values for these defines have been taken from the:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs".
 */
#define PMP_REGIONS_NUM 16

/**
 * Ibex PMP address granularity.
 *
 * Please see:
 * https://ibex-core.readthedocs.io/en/latest/03_reference/pmp.html#pmp-granularity
 */
#define PMP_GRANULARITY_IBEX 0

/**
 * RISC-V PMP address alignment and granularity.
 *
 * The values have been taken from the:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs", section "Address Matching".
 *
 * "PMP mechanism supports regions as small as four bytes, platforms may
 * specify coarser PMP regions."
 */
#define PMP_ADDRESS_MIN_ALIGNMENT 4
#define PMP_ADDRESS_MIN_ALIGNMENT_NAPOT 8
#define PMP_ADDRESS_ALIGNMENT (4 << PMP_GRANULARITY_IBEX)
#define PMP_ADDRESS_ALIGNMENT_MASK (PMP_ADDRESS_ALIGNMENT - 1)
#define PMP_ADDRESS_ALIGNMENT_INVERTED_MASK (~PMP_ADDRESS_ALIGNMENT_MASK)
#define PMP_ADDRESS_SHIFT 2
#define PMP_ADDRESS_SHIFT_NAPOT 3

/**
 * PMP region access permissions.
 *
 * PMP permissions are described in:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs", "Locking and Privilege Mode".
 *
 * Note that "The combination R=0 and W=1 is reserved for future use".
 *
 * When a region is configured with `kPmpRegionLockUnlocked` then these
 * permissions only apply to RISC-V "U" and "S" privilege modes, and have no
 * effect in the "M" mode.
 */
typedef enum pmp_region_permissions {
  kPmpRegionPermissionsNone = 0,         /**< No access permitted .*/
  kPmpRegionPermissionsReadOnly,         /**< Only read access. */
  kPmpRegionPermissionsExecuteOnly,      /**< Only execute access. */
  kPmpRegionPermissionsReadExecute,      /**< Read and execute access. */
  kPmpRegionPermissionsReadWrite,        /**< Read and write access. */
  kPmpRegionPermissionsReadWriteExecute, /**< Read, write and execute access. */
} pmp_region_permissions_t;

/**
 * PMP region locking.
 *
 * PMP locking is described in:
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6.1 Physical Memory Protection CSRs", "Locking and Privilege Mode".
 *
 * When a region is configured with `kPmpRegionLockLocked`, this region cannot
 * be accessed even by the machine "M" privilege code, and can be only unlocked
 * by the system reset. Additionally it also forces the
 * `pmp_region_permissions_t` access restrictions for the corresponding region
 * in machine "M" mode, which otherwise are ignored.
 */
typedef enum pmp_region_lock {
  kPmpRegionLockUnlocked = 0, /**< The region is unlocked. */
  kPmpRegionLockLocked,       /**< The region is locked. */
} pmp_region_lock_t;

/**
 * PMP region index is used to identify one of `PMP_REGIONS_NUM` PMP regions.
 */
typedef uint32_t pmp_region_index_t;

/**
 * PMP region configuration information.
 */
typedef struct pmp_region_config {
  pmp_region_lock_t lock; /**< Region lock for "M" privilege mode.*/
  pmp_region_permissions_t permissions; /**< Region access permissions. */
} pmp_region_config_t;

/**
 * PMP generic status codes.
 *
 * These error codes can be used by any function. However if a function
 * requires additional status codes, it must define a set of status codes to
 * be used exclusively by such function.
 */
typedef enum pmp_result {
  kPmpOk = 0, /**< Success. */
  kPmpError,  /**< General error. */
  kPmpBadArg, /**< Input parameter is not valid. */
} pmp_result_t;

/**
 * PMP region access and address configuration result.
 */
typedef enum pmp_region_configure_result {
  kPmpRegionConfigureOk = kPmpOk,
  kPmpRegionConfigureError = kPmpError,
  kPmpRegionConfigureBadArg = kPmpBadArg,
  /**
   * The requested region is invalid.
   */
  kPmpRegionConfigureBadRegion,
  /**
   * The requested address is invalid.
   */
  kPmpRegionConfigureBadAddress,
  /**
   * The requested region was not configured correctly. From the "Volume II:
   * RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified":
   * "Implementations will not raise an exception on writes of unsupported
   * values to a WARL field. Implementations can return any legal value on the
   * read of a WARL field when the last write was of an illegal value, but the
   * legal value returned should deterministically depend on the illegal
   * written value and the value of the field prior to the write"
   */
  kPmpRegionConfigureWarlError,
} pmp_region_configure_result_t;

/**
 * Disables PMP address matching.
 *
 * Address matching is disabled for `region`, however the corresponding
 * pmpaddr can still be used as a TOR range start address. For example, when
 * pmpcfgN is set to TOR, but pmpcfgN-1 is set to OFF, then pmpaddrN-1 can
 * be used as TOR range start address.
 *
 * Please see the PMP specification reference and general information at the
 * top of this header file.
 *
 * Note: this function will clear PMP `region` configuration.
 *
 * @param region PMP region to configure and set address for.
 * @param address System address.
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
pmp_region_configure_result_t pmp_region_configure_off(
    pmp_region_index_t region, uintptr_t address);

/**
 * PMP region access and address NA4 configuration result.
 */
typedef enum pmp_region_configure_na4_result {
  kPmpRegionConfigureNa4Ok = kPmpRegionConfigureOk,
  kPmpRegionConfigureNa4Error = kPmpRegionConfigureError,
  kPmpRegionConfigureNa4BadArg = kPmpRegionConfigureBadArg,
  kPmpRegionConfigureNa4BadRegion = kPmpRegionConfigureBadRegion,
  kPmpRegionConfigureNa4BadAddress = kPmpRegionConfigureBadAddress,
  kPmpRegionConfigureNa4WarlError = kPmpRegionConfigureWarlError,
  /**
   * NA4 is not available with granularity "G" > 0. Please see:
   * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
   * "3.6.1 Physical Memory Protection CSRs", "Table 3.10" and section
   * "Address Matching".
   */
  kPmpRegionConfigureNa4Unavailable,
} pmp_region_configure_na4_result_t;

/**
 * Configures PMP address matching to Naturally aligned four-byte (NA4).
 *
 * When pmpcfgN is set to NA4 then the protected region range is formed from
 * pmpaddrN and extends to the next 4 bytes.
 *
 * Please see the PMP specification reference and general information at the
 * top of this header file.
 *
 * @param region PMP region to configure and set the address for.
 * @param config PMP region configuration information.
 * @param address Range start system address.
 * @return `pmp_region_configure_na4_result_t`.
 */
PMP_WARN_UNUSED_RESULT
pmp_region_configure_na4_result_t pmp_region_configure_na4(
    pmp_region_index_t region, const pmp_region_config_t config,
    uintptr_t address);

/**
 * PMP region access and address NAPOT configuration result.
 */
typedef enum pmp_region_configure_napot_result {
  kPmpRegionConfigureNapotOk = kPmpRegionConfigureOk,
  kPmpRegionConfigureNapotError = kPmpRegionConfigureError,
  kPmpRegionConfigureNapotBadArg = kPmpRegionConfigureBadArg,
  kPmpRegionConfigureNapotBadRegion = kPmpRegionConfigureBadRegion,
  kPmpRegionConfigureNapotBadAddress = kPmpRegionConfigureBadAddress,
  kPmpRegionConfigureNapotWarlError = kPmpRegionConfigureWarlError,
  /**
   * NAPOT size must be at least 8bytes and Power Of Two. NAPOT address
   * must be aligned to the size. Please see:
   * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
   * "3.6.1 Physical Memory Protection CSRs", "Table 3.10" and section
   * "Address Matching".
   */
  kPmpRegionConfigureNapotBadSize,
} pmp_region_configure_napot_result_t;

/**
 * Configures PMP address matching to Naturally aligned power-of-two (NAPOT).
 *
 * Size ≥ 8 bytes. When pmpcfgN is set to NAPOT then the protected region range
 * is formed from a single encoded pmpaddrN address. NAPOT ranges make use of
 * the low-order bits of the associated address register to encode the size of
 * the range, please see the table "3.10" of the "Address Matching" section of
 * the specification mentioned above.
 *
 * Example: NAPOT encoded address of yyyy011 describes the
 * yyyy00000 .. yyyy11111 range. The index of the first "0", determines the
 * range size ( 2^(3 + index) ).
 *
 * Please see the PMP specification reference and general information at the
 * top of this header file.
 *
 * @param region PMP region to configure and set the address for.
 * @param config PMP region configuration information.
 * @param address Range start system address (must be aligned to `size`).
 * @param size Address range size (must be power-of-two).
 * @return `pmp_region_configure_napot_result_t`.
 */
PMP_WARN_UNUSED_RESULT
pmp_region_configure_napot_result_t pmp_region_configure_napot(
    pmp_region_index_t region, const pmp_region_config_t config,
    uintptr_t address, uint32_t size);

/**
 * Configures PMP address matching to Top Of the Range (TOR).
 *
 * When pmpcfgN is set to TOR, the protected address range is formed from the
 * pmpaddrN-1 and pmpaddrN registers. Note that the combination of pmpcfgN set
 * to TOR and pmpcfgN-1 set to NAPOT does not form any meaningful range for TOR
 * addressing mode. pmpcfgN TOR mode will take the bottom of the range
 * pmpaddrN-1 address as is, without decoding the NAPOT address.
 *
 * Please see the PMP specification reference and general information at the
 * top of this header file.
 *
 * @param region_end PMP region to configure and set the address for.
 * @param config PMP region configuration information.
 * @param address_start Bottom of the range system address. Must be
 *        0 for the "0" region.
 * @param address_end Top of the range system address.
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
pmp_region_configure_result_t pmp_region_configure_tor(
    pmp_region_index_t region_end, const pmp_region_config_t config,
    uintptr_t address_start, uintptr_t address_end);

/**
 * Queries the lock status for the requested region.
 *
 * @param region PMP region to query the lock information for.
 * @param lock State of the PMP region (locked/unlocked).
 * @return `pmp_region_configure_result_t`.
 */
PMP_WARN_UNUSED_RESULT
pmp_region_configure_result_t pmp_region_lock_status_get(
    pmp_region_index_t region, pmp_region_lock_t *lock);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PMP_H_
