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
 * Address translation slot selection.
 */
typedef enum dif_rv_core_ibex_addr_translation_slot {
  kDifRvCoreIbexAddrTranslationSlot_0,
  kDifRvCoreIbexAddrTranslationSlot_1,
  kDifRvCoreIbexAddrTranslationSlotCount,
} dif_rv_core_ibex_addr_translation_slot_t;

/**
 * Address translation bus selection.
 */
typedef enum dif_rv_core_ibex_addr_translation_bus {
  kDifRvCoreIbexAddrTranslationDBus,
  kDifRvCoreIbexAddrTranslationIBus,
  kDifRvCoreIbexAddrTranslationBusCount,
} dif_rv_core_ibex_addr_translation_bus_t;

/**
 * Address translation matching region.
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
typedef struct dif_rv_core_ibex_addr_translation_mapping {
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
} dif_rv_core_ibex_addr_translation_mapping_t;

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

typedef enum dif_rv_core_ibex_rnd_status_code {
  /**
   * The current rnd word is valid.
   */
  kDifRvCoreIbexRndStatusValid = 1 << 0,
  /**
   * The current rnd word is fips compliant.
   */
  kDifRvCoreIbexRndStatusFipsCompliant = 1 << 1,
} dif_rv_core_ibex_rnd_status_code_t;

/**
 * Bitmask with the `dif_rv_core_ibex_rnd_status_code_t` values.
 */
typedef uint32_t dif_rv_core_ibex_rnd_status_t;

/**
 * NMI enabled status and current state.
 */
typedef struct dif_rv_core_ibex_nmi_state {
  /**
   * NMI alert is currently enabled.
   */
  bool alert_enabled;
  /**
   * Alert has been raised.
   */
  bool alert_raised;
  /**
   * NMI watchdog is currently enabled.
   */
  bool wdog_enabled;
  /**
   * Watchdog has barked.
   */
  bool wdog_barked;
} dif_rv_core_ibex_nmi_state_t;

typedef enum dif_rv_core_ibex_nmi_source {
  /**
   * NMI alert handler.
   */
  kDifRvCoreIbexNmiSourceAlert = 1 << 0,
  /**
   * NMI watchdog bark.
   */
  kDifRvCoreIbexNmiSourceWdog = 1 << 1,
  /**
   * All ibex NMIs.
   */
  kDifRvCoreIbexNmiSourceAll = 0x3,
} dif_rv_core_ibex_nmi_source_t;

typedef struct dif_rv_core_ibex_crash_dump_state {
  /**
   * The last exception address.
   */
  uint32_t mtval;

  /**
   * The last exception PC.
   */
  uint32_t mpec;

  /**
   * The last data access address.
   */
  uint32_t mdaa;

  /**
   * The next PC.
   */
  uint32_t mnpc;

  /**
   * The current PC.
   */
  uint32_t mcpc;
} dif_rv_core_ibex_crash_dump_state_t;

typedef struct dif_rv_core_ibex_previous_crash_dump_state {
  /**
   * The exception address for the previous crash.
   */
  uint32_t mtval;

  /**
   * The last exception PC for the previous crash.
   */
  uint32_t mpec;
} dif_rv_core_ibex_previous_crash_dump_state_t;

/**
 * Under normal circumstances, only the current crash dump state is valid. When
 * the CPU encounters a double fault, the current crash dump is moved to
 * previous, and the new crash dump is shown in current.
 */
typedef struct dif_rv_core_ibex_crash_dump_info {
  /**
   * The crash dump state for the current execution.
   */
  dif_rv_core_ibex_crash_dump_state_t fault_state;

  /**
   * The crash dump state for the previous execution. It will only contain valid
   * data in case of a double fault, which will be indicated by the
   * `double_fault` member.
   */
  dif_rv_core_ibex_previous_crash_dump_state_t previous_fault_state;

  /**
   * `kDifToggleEnabled` if a double fault happened, otherwise
   * `kDifToggleDisabled`
   */
  dif_toggle_t double_fault;
} dif_rv_core_ibex_crash_dump_info_t;

/**
 * Configure address translation for
 * the given `bus` (either instruction or data) in the `slot`.
 *
 * @param rv_core_ibex Handle.
 * @param slot   Slot to be used.
 * @param bus    Bus to be translated.
 * @param addr_map Address mapping description.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_configure_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus,
    dif_rv_core_ibex_addr_translation_mapping_t addr_map);

/**
 * Enable address translation for
 * the given `bus` (either instruction or data) in the `slot`.
 *
 * @param rv_core_ibex Handle.
 * @param slot   Slot to be used.
 * @param bus    Bus to be translated.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_enable_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus);

/**
 * Disable address translation for
 * the given `bus` (either instruction or data) in the `slot`.
 *
 * @param rv_core_ibex Handle.
 * @param slot   Slot to be used.
 * @param bus    Bus to be translated.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_disable_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus);

/**
 * Read a discription of the address mapping configured on a given `slot`
 * for a given `bus`.
 *
 * @param rv_core_ibex Handle.
 * @param slot Slot of interest.
 * @param bus Bus of interest.
 * @param[out] addr_map Description of address mapping.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_read_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus,
    dif_rv_core_ibex_addr_translation_mapping_t *addr_map);

/**
 * Lock the address translation settings for a given `slot` and `bus` registers.
 * Once locked it can no longer be unlocked until the next system reset. This
 * function will quietly do nothing if the settings are already locked.
 *
 * @param rv_core_ibex Handle.
 * @param slot Slot to be locked.
 * @param bus Translated bus to be locked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_lock_addr_translation(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_addr_translation_slot_t slot,
    dif_rv_core_ibex_addr_translation_bus_t bus);

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

/**
 * Enables NMI support for security alert events and watchdog bark.
 *
 * @param rv_core_ibex Handle.
 * @param nmi A bitmask with nmi sources to be enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_enable_nmi(const dif_rv_core_ibex_t *rv_core_ibex,
                                         dif_rv_core_ibex_nmi_source_t nmi);

/**
 * Read the NMI enable status and current event state.
 *
 * @param rv_core_ibex Handle.
 * @param[out] nmi_state The nmi state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_get_nmi_state(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_nmi_state_t *nmi_state);

/**
 * Clear the NMI current event state.
 *
 * @param rv_core_ibex Handle
 * @param nmi A bitmask with nmi sources to be cleared.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_clear_nmi_state(
    const dif_rv_core_ibex_t *rv_core_ibex, dif_rv_core_ibex_nmi_source_t nmi);

/**
 * Gets whether the rnd data is either valid or is FIPS compliant.
 *
 * @param rv_core_ibex Handle.
 * @param[out] status Pointer to be filled with the current rnd status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_get_rnd_status(
    const dif_rv_core_ibex_t *rv_core_ibex,
    dif_rv_core_ibex_rnd_status_t *status);

/**
 * Reads a random word from the RISC-V Ibex core wrapper.
 *
 * @param rv_core_ibex Handle.
 * @param[out] data Pointer to be filled with the random word.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_read_rnd_data(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t *data);

typedef uint32_t dif_rv_core_ibex_fpga_info_t;

/**
 * Read the FPGA build timestamp info. This function only returns valid data for
 * fpga environments, for all other environments it is simply 0.
 *
 * @param rv_core_ibex Handle.
 * @param[out] info A pointer to receive the FPGA timestamp info.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_read_fpga_info(
    const dif_rv_core_ibex_t *rv_core_ibex, dif_rv_core_ibex_fpga_info_t *info);

/**
 * Software fatal alert. When triggered,
 * a fatal alert is sent. Note, this alert once cleared cannot be set and
 * will continuously cause alert events.
 */

/**
 * Get the software recoverable alert sate.
 *
 * @param rv_core_ibex Handle.
 * @param[out] enabled Returns `true` if enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT dif_result_t dif_rv_core_ibex_get_sw_recov_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex, bool *enabled);

/**
 * Software recoverable alert. When triggered, a recoverable alert is sent. Once
 * the alert is sent, the register is then reset to disabled.
 *
 * @param rv_core_ibex Handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_trigger_sw_recov_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex);

/**
 * Get the software fatal alert trigger status.
 *
 * @param rv_core_ibex Handle.
 * @param[out] enabled Returns `true` if enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_get_sw_fatal_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex, bool *enabled);

/**
 * Software fatal alert. When triggered, a fatal alert is sent. Note, once this
 * alert is triggered it cannot be reset and will continuously cause alert
 * events.
 *
 * @param rv_core_ibex Handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_trigger_sw_fatal_err_alert(
    const dif_rv_core_ibex_t *rv_core_ibex);

/**
 * Parse the cpu info read from the rstmgr.
 *
 * @param rv_core_ibex Handle.
 * @param cpu_info Buffer with the cpu info read from the rstmgr.
 * @param cpu_info_len The amount of words in the `cpu_info` buffer.
 * @param[out] crash_dump_info Parsed dump.
 * @return  The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_parse_crash_dump(
    const dif_rv_core_ibex_t *rv_core_ibex, uint32_t *cpu_info,
    uint32_t cpu_info_len, dif_rv_core_ibex_crash_dump_info_t *crash_dump_info);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_RV_CORE_IBEX_H_
