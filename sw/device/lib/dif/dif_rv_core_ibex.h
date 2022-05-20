// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_CORE_IBEX_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_CORE_IBEX_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_rv_core_ibex_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Address translation slot.
 */
typedef enum dif_rv_core_ibex_addr_translation_slot {
  kDifRvCoreIbexAddrTranslationSlot_0,
  kDifRvCoreIbexAddrTranslationSlot_1,
  kDifRvCoreIbexAddrTranslationSlotCount,
} dif_rv_core_ibex_addr_translation_slot_t;

/**
 * Address tranlation matching region.
 *
 * The value programmed is done at power-of-2 alignment. For example, if the
 * intended matching region is 0x8000_0000 to 0x8000_FFFF, the value
 * programmed is 0x8000_7FFF.
 *
 * The value programmed can be determined from the translation granule. Assume
 * the user wishes to translate a specific 64KB block to a different address:
 * 64KB has a hex value of 0x10000. Subtract 1 from this value and then right
 * shift by one to obtain 0x7FFF. This value is then logically OR'd with the
 * upper address bits that would select which 64KB to translate.
 */
typedef struct dif_rv_core_ibex_addr_translation_pair {
  /**
   * Matching address (Virtual address).
   * When an incoming transaction matches the matching
   * region, it is redirected to the new address. If a transaction does not
   * match, then it is directly passed through.
   */
  uintptr_t matching_addr;

  /**
   * Remap address (Physical address).
   * The region where the matched transtaction will be
   * redirected to.
   */
  uintptr_t remap_addr;

  /**
   * Address region size.
   */
  size_t size;
} dif_rv_core_ibex_addr_translation_pair_t;

/**
 * Addresses translation region.
 */
typedef struct dif_rv_core_ibex_addr_translation_region {
  /**
   * Region representing the instruction bus.
   */
  dif_rv_core_ibex_addr_translation_pair_t ibus;

  /**
   * Region representing the data bus.
   */
  dif_rv_core_ibex_addr_translation_pair_t dbus;
} dif_rv_core_ibex_addr_translation_region_t;

/**
 * Ibex error status detected by `rv_core_ibex` peripheral.
 */
typedef enum dif_rv_core_ibex_error_status {
  /**
   * Register transmission integrity error.
   */
  kDifRvCoreIbexErrorStatusRegisterTransmissionIntegrity = 1 << 0,

  /**
   * Response integrity error.
   */
  kDifRvCoreIbexErrorStatusFatalResponseIntegrity = 1 << 8,

  /**
   * Fatal internal error (`alert_major_internal_o` from Ibex seen).
   */
  kDifRvCoreIbexErrorStatusFatalInternalError = 1 << 9,

  /**
   * recoverable internal error (`alert_minor` from Ibex seen).
   */
  kDifRvCoreIbexErrorStatusRecoverableInternal = 1 << 10,

  /**
   * All errors combined.
   */
  kDifRvCoreIbexErrorStatusAll = (1 << 0 | 1 << 8 | 1 << 9 | 1 << 10),
} dif_rv_core_ibex_error_status_t;

/**
 * Configure the instruction and data bus in the address translation `slot`.
 *
 * @param rv_core_ibex Handle.
 * @param slot   Slot to be used.
 * @param region Dbus and Ibus addresses.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_configure_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_region_t region);

/**
 *
 * @param rv_core_ibex Handle.
 * @param slot Slot to be read.
 * @param[out] region Pointer to receive the Dbus and Ibus addresses.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_read_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_region_t *region);

/**
 * Lock the `slot` registers. Once locked it can no longer be unlocked until the
 * next system reset.
 *
 * @param rv_core_ibex Handle.
 * @param slot Slot to be locked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_lock_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot);

/**
 * Read the ibex error status.
 *
 * @param rv_core_ibex Handle.
 * @param error_status Pointer to receive the error status value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_get_error_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_error_status_t *error_status);

/**
 * Clear the ibex error status, after the software has handled it.
 *
 * @param rv_core_ibex Handle.
 * @param error_status The error to be cleared.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_clear_error_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_error_status_t error_status);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_CORE_IBEX_H_
