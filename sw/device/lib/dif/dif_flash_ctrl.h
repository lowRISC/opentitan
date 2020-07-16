// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/flash_ctrl/doc/">Flash controller</a> Device Interface
 * Functions
 */
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // _cplusplus

/**
 * Configuration for initializing the flash controller device.
 */
typedef struct dif_flash_ctrl_config {
  /**
   * The base address for registers in the flash controller device.
   */
  mmio_region_t base_addr;
} dif_flash_ctrl_config_t;

/**
 * Carries state for a flash controller device.
 *
 * All members should be considered private and should not be accessed directly
 * outside of the DIF implementation. This struct is only public for allocation
 * purposes.
 */
typedef struct dif_flash_ctrl {
  /**
   * The base address for registers in the flash controller device.
   */
  mmio_region_t base_addr;

  /**
   * The number of words transfered from the start of the latest program/read
   * transaction.
   */
  uint32_t words_transfered;
} dif_flash_ctrl_t;

/**
 * Base result type for functions that may produce generic errors.
 */
typedef enum dif_flash_ctrl_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlOk = 0,
  /**
   * An unknown error occurred.
   *
   * This error is not recoverable.
   */
  kDifFlashCtrlError = 1,
  /**
   * An invalid argument was provided.
   *
   * This error is recoverable and indicates the function produced no side
   * effects.
   *
   * In order to recover from this error the caller must be aware of the
   * possibility of passing invalid arguments and correct these arguments in
   * future calls.
   */
  kDifFlashCtrlBadArg = 2,
} dif_flash_ctrl_result_t;

/**
 * Initializes the flash controller device described by `config`, writing
 * internal state to `flash_ctrl_out`.
 *
 * This function must be called to obtain a valid `dif_flash_ctrl_t` for use in
 * all other functions of this DIF.
 *
 * @param config Configuration for this flash controller device.  @param
 * flash_ctrl_out An out-parameter to hold internal flash controller state.
 * @return `kDifFlashCtrlBadArg` if `config` or `flash_ctrl_out `is null,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_init(
    const dif_flash_ctrl_config_t *config, dif_flash_ctrl_t *flash_ctrl_out);

/**
 * Interrupt signals for flash_ctrl.
 *
 * Enumeration used to enable, disable, test, and query the flash_ctrl
 * interrupts. Please see the comportability specification for more information:
 * https://docs.opentitan.org/doc/rm/comportability_specification/
 */
typedef enum dif_flash_ctrl_irq {
  kDifFlashCtrlIrqProgEmpty,
  kDifFlashCtrlIrqProgLevel,
  kDifFlashCtrlIrqRdFull,
  kDifFlashCtrlIrqRdLevel,
  kDifFlashCtrlIrqOpDone,
} dif_flash_ctrl_irq_t;

/**
 * Generic enable/disable enumeration.
 */
typedef enum dif_flash_ctrl_enable {
  /**
   * Generic enable.
   */
  kDifFlashCtrlEnable = 0,
  /**
   * Generic disable.
   */
  kDifFlashCtrlDisable,
} dif_flash_ctrl_enable_t;

/**
 * Get the state of the requested IRQ in `irq_type`.
 *
 * @param flash_ctrl flash controller state data.
 * @param irq_type IRQ to get the state of.
 * @param state IRQ state passed back to the caller.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t *state);

/**
 * Clear the state of the requested IRQ in `irq_type`.
 *
 * Primary use of this
 * function is to de-assert the interrupt after it has been serviced.
 *
 * @param flash_ctrl flash controller state data.
 * @param irq_type IRQ to be de-asserted.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_clear(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type);

/**
 * Disable generation of all flash controller interrupts, and pass previous
 * interrupt state in `state` back to the caller.
 *
 * Parameter `state` is ignored if null.
 *
 * @param flash_ctrl flash controller state data.
 * @param state IRQ state passed back to the caller.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irqs_disable(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *state);

/**
 * Restore previous flash controller IRQ state.
 *
 * This function is used to restore the flash controller interrupt state prior
 * to `dif_flash_ctrl_irqs_disable` function call.
 *
 * @param flash_ctrl flash controller state data.
 * @param state IRQ state to restore.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irqs_restore(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t state);

/**
 * Enable/disable an flash controller interrupt specified in `enable`.
 *
 * @param flash_ctrl flash controller state data.
 * @param irq_type flash controller interrupt type.
 * @param enable enable or disable the interrupt.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_control(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t enable);

/**
 * Force interrupt specified in `irq_type`.
 *
 * @param flash_ctrl flash controller state data.
 * @param irq_type flash controller interrupt type to be forced.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_force(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type);

/**
 * Enumeration to describe the program operation type.
 */
typedef enum dif_flash_ctrl_program_type {
  /**
   * Normal program operation to flash.
   */
  kDifFlashCtrlProgramNormal,
  /**
   * Repair program operation to flash. Whether this is actually supported
   * depends on the underlying flash memory.
   */
  kDifFlashCtrlProgramRepair,
} dif_flash_ctrl_program_type_t;

/**
 * Erase operation mode enumeration.
 */
typedef enum dif_flash_ctrl_erase_type {
  /**
   * Erase 1 page of flash.
   */
  kDifFlashCtrlEraseSelPage,
  /**
   * Erase 1 bank of flash.
   */
  kDifFlashCtrlEraseSelBank,
} dif_flash_ctrl_erase_type_t;

/**
 * Region selection enumeration. Represents both the partition and the info
 * type.
 */
typedef enum dif_flash_crtl_region_select {
  /**
   * Select the data partition.
   */
  kDifFlashCtrlRegionData,
  /**
   * Select the info partition of type 1.
   */
  kDifFlashCtrlRegionInfo0,
  /**
   * Select the info partition of type 1.
   */
  kDifFlashCtrlRegionInfo1,
  /**
   * Select the info partition of type 1.
   */
  kDifFlashCtrlRegionInfo2,
} dif_flash_ctrl_region_select_t;

/**
 * Check if the underlying flash memory supports the
 * `kDifFlashCtrlProgramRepair` program type is supported.
 *
 * @param flash_ctrl The flash controller to check.
 * @param support_out Out-parameter, `true` if the underlying flash hardware
 * supports repairs, `false` oterwise.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `support_out` is NULL,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_t dif_flash_ctrl_repair_support_check(
    const dif_flash_ctrl_t flash_ctrl, bool *support_out);

/**
 * Result type for configuration transactions that may fail if flash controller
 * is in an invalid state.
 */
typedef enum dif_flash_ctrl_start_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlStartOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlStartError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlStartBadArg = kDifFlashCtrlBadArg,
  /**
   * A flash operation is in progress.
   *
   * This error is recoverable and indicates the function produced no side
   * effects.
   *
   * When a flash operation is in progress the control register cannot be
   * updated. This error can be recovered from by waiting for the flash
   * operation to complete.
   */
  kDifFlashCtrlStartBusy,
  /**
   * The underlying flash memory doesn't support the repair program operation.
   *
   * This error is recoverable and indicates the function produced no side
   * effects.
   */
  kDifFlashCtrlStartRepairNotSupported,
} dif_flash_ctrl_start_result_t;

/**
 * Start a read transaction.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will perform a read
 * at address 0x10.
 *
 * Not all underlying flash memory supports the `kDifFlashCtrlProgramRepair`
 * mode. When specifying this as the `type`,
 * `dif_flash_ctrl_repair_support_check()` can first be used to ensure the
 * operation is supported. If a repair operation is requested and not supported
 * by the underlying hardware, the `kDfiFlashCtrlStartRepairNotSupported` error
 * will be returned from this function.
 *
 * @param flash_ctrl flash controller device to execute the transaction on.
 * @param addr The address to read.
 * @param word_count The number of bus words the flash operation should read.
 * @param region The region to read from.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_read_start(
    dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count,
    dif_flash_ctrl_region_select_t region);

/**
 * Start a program transaction.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will perform a read
 * at address 0x10.
 *
 * @param flash_ctrl flash controller device to execute the transaction on.
 * @param addr The address to program.
 * @param word_count The number of bus words the flash operation should program.
 * @param program_type The flash operation type, either normal or repair mode.
 * @param region The region to write to.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_prog_start(
    dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count,
    dif_flash_ctrl_program_type_t program_type,
    dif_flash_ctrl_region_select_t reigon);

/**
 * Start an erase transaction.
 *
 * For page erases, the controller will truncate to the closest lower page
 * aligned address. For bank erases, the controller will truncate to the closest
 * lower bank aligned address.
 *
 * @param flash_ctrl flash controller device to execute the transaction on.
 * @param addr The address to read.
 * @param erase_type The erase mode.
 * @param region The region to delete on.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_erase_start(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr,
    dif_flash_ctrl_erase_type_t erase_type,
    dif_flash_ctrl_region_select_t region);

/**
 * Result type for memory protection configuration actions.
 */
typedef enum dif_flash_ctrl_region_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlRegionOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlRegionError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlRegionBadArg = kDifFlashCtrlBadArg,
  /**
   * Region cannot be configured.
   *
   * This error indicates the function produced no side effects.  Once the flash
   * region configuration registers have been locked they can't be written to
   * until the next reset. A function that produces this error will continue
   * producing errors on all subsequent calls until the device is reset.
   */
  kDifFlashCtrlRegionBadAccess,
} dif_flash_ctrl_region_result_t;

/**
 * Representation of the memory protection regions for the info pages.
 */
typedef struct dif_flash_ctrl_info_region {
  /**
   * The bank.
   */
  uint32_t bank;
  /**
   * The info type to use.
   */
  uint32_t type;
  /**
   * The page number.
   */
  uint32_t page;
} dif_flash_ctrl_info_region_t;

typedef enum dif_flash_ctrl_region_type {
  /**
   * Represents the data regions.
   */
  kDifFlashCtrlRegionTypeData,
  /**
   * Represents the info regions.
   */
  kDifFlashCtrlRegionTypeInfo,
  /**
   * Represents the default region.
   */
  kDifFlashCtrlRegionTypeDefault,
} dif_flash_ctrl_region_type_t;

/**
 * Tagged union for representing all memory protection regions.
 */
typedef struct dif_flash_ctrl_region {
  /**
   * The region's type.
   */
  dif_flash_ctrl_region_type_t type;
  /**
   * Description of the region.
   *
   * The union should be able to resolve a valid `data` for the
   * `kDifFlashCtrlRegionTypeData` tag in `type`, or a valid `info` for the
   * `kDifFlashCtrlRegionTypeInfo` tag in `type`.
   *
   * For `kDifFlashCtrlRegionDefault` `type`s this field is ignored.
   */
  union {
    uint32_t data;
    dif_flash_ctrl_info_region_t info;
  } region;
} dif_flash_ctrl_region_t;

/**
 * Enable/disable the region of flash indexed by `region`.
 *
 * This is not supported for the default region.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl flash controller device to configure.
 * @param region The region to operate on.
 * @param enable Enable or disable this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_enable_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the enabled/disabled state for this region.
 *
 * This is not supported for the default region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable_out Out-parameter, the enabled/disabled state of this region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_enable_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Region access access bits.
 */
typedef struct dif_flash_ctrl_access {
  /**
   * Read access.
   *
   * Indicates read access for a particular region.
   */
  bool read;
  /**
   * Program access.
   *
   * Indicates write access for a particular region.
   */
  bool program;
  /**
   * Erase access.
   *
   * Indicates erase capabilities for a particular region.
   */
  bool erase;
} dif_flash_ctrl_access_t;

/**
 * Set access permissions for the region of flash indexed by `region`.
 *
 * Read, program, and erase permissions can be enabled/disabled depending on the
 * values of `access`.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl flash controller device to configure.
 * @param region The region to operate on.
 * @param access The access type to control for this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_access_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_access_t access);

/**
 * Get the access permissions for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param access_out Out-parameter, a reference to a `dif_flash_ctrl_access_t`
 * struct for writing the access permissions to for this region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `access_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_access_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_access_t *access_out);

/**
 * Set the scramble mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable Enable or disable flash scrambling for this region.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_scramble_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the scramble mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable_out Out-parameter, for writing the scramble mode for this
 * region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_scramble_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Set the ECC mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable Enable or disable error correction for this region.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_ecc_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the ECC mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable_out Out-parameter, for writing the error correction mode for
 * this region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_ecc_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Set the High Endurance mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable Enable or disable High Endurance mode for this region.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_he_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the High Endurance mode for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param enable_out Out-parameter, for writing the High Endurance mode for
 * this region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_he_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Set the base page for this region.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl flash controller device to configure.
 * @param region The region to operate on.
 * @param page The starting page for this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` or
 * `page` is invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has
 * been locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_data_region_base_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t page);

/**
 * Get the base page for this region.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param page_out Out-parameter, the base page for this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_data_region_base_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *page_out);

/**
 * Set the size of this region in number of pages.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl flash controller device to configure.
 * @param region The region to operate on.
 * @param size The `region` size in number of pages.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_data_region_size_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t size);

/**
 * Get the size of this region in number of pages.
 *
 * @param flash_ctrl flash controller device to query.
 * @param region The region in question.
 * @param size_out Out-parameter, the number of pages in this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_data_region_size_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *size_out);

/**
 * Lock memory region configuration until the device is reset.
 *
 * This will prevent any further configuration of memory regions until device
 * reset. Future calls to region configuration functions will return
 * `kDifFlashCtrlRegionBadAccess`.
 *
 * @param flash_ctrl flash controller device to lock region configuration on.
 * @param region The region to lock.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null, or if `region`
 * is invalid, `kDifFlashCtrlRegionBadAccess` if configuration is already
 * locked, `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_config_lock(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region);

/**
 * Query the state of the memory region configuration registers.
 *
 * This function checks if memory region configuration is still enabled or if
 * has been locked. Once locked, region configuration cannot be enabled again,
 * and all calls to region configuration functions will return
 * `kDifFlashCtrlRegionBadAccess` until the device is restarted.
 *
 * @param flash_ctrl flash controller device to check the lock state for.
 * @param region The region in question.
 * @param access_out Out-parameter, the current state of memory region
 * configuration access.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `access_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_region_config_check(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_region_t region,
    dif_flash_ctrl_enable_t *access_out);

/**
 * Result type for bank configuration actions.
 */
typedef enum dif_flash_ctrl_bank_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlBankOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlBankError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlBankBadArg = kDifFlashCtrlBadArg,
  /**
   * Region cannot be configured.
   *
   * This error indicates the function produced no side effects.
   *
   * Once bank configuration has been locked the associated registers cannot be
   * written to until the next reset. A function that produces this error will
   * continue producing errors on all subsequent calls until the device is
   * reset.
   */
  kDifFlashCtrlBankLocked,
} dif_flash_ctrl_bank_result_t;

/**
 * Enable/disable erase operations for a particular flash bank.
 *
 * This may only be done if bank configuration is still enabled.
 *
 * @param flash_ctrl flash controller device to operate on.
 * @param bank The bank to configure.
 * @param erase_enable Enable/disable erase access for this bank.
 * @return `kDifFlashCtrlBankBadArg` if `flash_ctrl` is null or `bank` is
 * invalid, `kDifFlashCtrlBankBadAccess` if bank configuration is locked, and
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_bank_result_t dif_flash_ctrl_bank_erase_enable(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t bank,
    dif_flash_ctrl_enable_t erase_enable);

/**
 * Query the erase permissions for a particular flash bank.
 *
 * @param flash_ctrl flash controller device to query.
 * @param bank The bank to query.
 * @param erase_enable_out Out-parameter, the erase permissions for this bank.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `erase_enable_out` is null
 * and `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_bank_erase_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t bank,
    dif_flash_ctrl_enable_t *erase_enable_out);

/**
 * Lock bank configuration until the device is reset.
 *
 * This will prevent any further configuration of memory banks until device
 * reset. Future calls to bank configuration functions will return
 * `kDifFlashCtrlBankBadAccess`.
 *
 * @param flash_ctrl flash controller device to lock region configuration on.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_lock(
    const dif_flash_ctrl_t *flash_ctrl);

/**
 * Query the state of the bank configuration registers.
 *
 * This function checks if memory bank configuration is still enabled or if
 * has been locked. Once locked, bank configuration cannot be enabled again,
 * and all calls to bank configuration functions will return
 * `kDifFlashCtrlBankBadAccess` until the device is restarted.
 *
 * @param flash_ctrl flash controller device to check the lock state for.
 * @param access_out Out-parameter, the current state of bank configuration
 * access.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `access_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_is_enabled(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t *access_out);

/**
 * Status bits that can be queried.
 */
typedef struct dif_flash_ctrl_status {
  /**
   * Flash read FIFO full, software must consume data.
   */
  bool rd_full;
  /**
   * Flash read FIFO empty.
   */
  bool rd_empty;
  /**
   * Flash program FIFO full.
   */
  bool prog_full;
  /**
   * Flash program FIFO empty, software must provide data.
   */
  bool prog_empty;
  /**
   * Flash controller undergoing init.
   */
  bool init_wip;
  /**
   * Flash operation done.
   */
  bool done;
  /**
   * Flash operation error.
   */
  bool err;
} dif_flash_ctrl_status_t;

/**
 * Query the status registers on the flash controller.
 *
 * This funciton checks the various status bits as described in
 * `dif_flash_ctrl_status_t`.
 *
 * @param flash_ctrl flash controller device to check the status bits for.
 * @param status_out Out-parameter, the current status of the flash controller.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `status_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_status_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_status_t *status_out);

/**
 * Result type for querying error information.
 */
typedef enum dif_flash_ctrl_error_query_result {
  /**
   * No error occurred during this call.
   *
   * This indicates the flash controller is in an error state and, calls to
   * query information about this error are appropriate.
   */
  kDifFlashCtrlErrorQueryOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlErrorQueryError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlErrorQueryBadArg = kDifFlashCtrlBadArg,
  /**
   * This query is invalid because the flash controller is not in an error
   * state.
   *
   * This error is recoverable and indicates the function produced no side
   * effects.
   */
  kDifFlashCtrlErrorQueryInvalid,
} dif_flash_ctrl_error_query_result_t;

/**
 * Retrieve error information from the flash controller.
 *
 * This is only relevant if the `err` bit is set, which can be queried through
 * `dif_flash_ctrl_status_get()`. Calling this function will clear the `err`
 * bit
 *
 * A null value for `address_out` is valid and can be useful if the caller just
 * wants to clear the `err` status bit.
 *
 * @param flash_ctrl flash controller device to query error info for.
 * @param address_out Out-parameter, the error address. May be null.
 * @return `kDifFlashCtrlErrorQueryBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlErrorQueryInvalid` if the flash controller is not in an error
 * state, and `kDifFlashCtrlErrorQueryOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_error_query_result_t dif_flash_ctrl_error_describe(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *address_out);

/**
 * Set the interrupt watermarks for the program FIFO.
 *
 * The value of `prog` defines the level the program FIFO must drain to before
 * triggering a `prog_lvl` interrupt.
 *
 * This interrupts will only trigger if enabled through the interrupt API.
 *
 * @param flash_ctrl flash controller to set FIFO level watermarks for.
 * @param prog Trigger an interrupt when the program FIFO drains to this level.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null or if the value `rd` is
 * out of range, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_fifo_prog_lvl_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t prog);

/**
 * Set the interrupt watermarks for the read FIFO.
 *
 * The value of `rd` defines the level the read FIFO must fill to before
 * triggering a `rd_lvl` interrupt.
 *
 * This interrupt will only trigger if enabled through the interrupt API.
 *
 * @param flash_ctrl flash controller to set FIFO level watermarks for.
 * @param rd Trigger an interrupt when the read FIFO fills to this level.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null or if the value of
 * `prog` is out of range, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_fifo_rd_lvl_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t rd);

/**
 * Get the interrupt watermarks for the program and read FIFOs.
 *
 * @sa #dif_flash_ctrl_fifo_lvl_set()
 *
 * @param flash_ctrl flash controller to get FIFO level watermarks from.
 * @param prog_out Out-parameter, trigger an interrupt when the program FIFO
 * drains to this level. May be null.
 * @param rd_out Out-parameter, trigger an interrupt when the read FIFO fills to
 * this level. May be null.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_fifo_lvl_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *prog_out, uint32_t *rd_out);

/**
 * Resets both the program and read FIFOs.
 *
 * This is useful in the event of an unexpected error as a means of reseting
 * state.
 *
 * @param flash_ctrl flash controller device to clear FIFOs on.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_fifo_reset(
    const dif_flash_ctrl_t *flash_ctrl);

/**
 * Result type for operations on the program FIFO.
 */
typedef enum dif_flash_ctrl_prog_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlProgOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlProgError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlProgBadArg = kDifFlashCtrlBadArg,
  /**
   * A program operation was not initiated.
   *
   * This error is recoverable and indicates the function produced no side
   * effects.
   *
   * Before writing to the program FIFO a program operation must first be
   * started. This can be recovered with a call to
   * `dif_flash_ctrl_prog_start()`.
   */
  kDifFlashCtrlProgInactive,
  /**
   * The program FIFO filled up.
   *
   * This error is recoverable by waiting for space to free up on the program
   * FIFO.
   */
  kDifFlashCtrlProgFull,
} dif_flash_ctrl_prog_result_t;

/**
 * Push data to the program FIFO.
 *
 * Attempts to write the contents of `data` to the program FIFO. It is required
 * that a program transaction be started prior to calling this function, else
 * the call will fail with `kDifFlashCtrlProgInactive`.
 *
 * The following conditions are also required:
 *   - `data` must reference a contiguous, allocated, readable region of at
 *     least `word_count` words, violation of this will produce undefined
 *     behavior.
 *   - The first call to this function after starting the program transaction
 *     the same `word_count` must not exceed what was supplied at the start of
 * the program transaction.
 *   - Each subsequent call the new `word_count` must not exceed `word_count -
 *     words_sent_out` from the previous call.
 * All deviations on the above will produce a `kDifFlashCtrlProgBadArg` error
 * unless otherwise specified.
 *
 * If the FIFO fills up this function may return `kDifFlashCtrlProgFull`
 * indicating that not all data was written and this function must be called
 * again once space has freed up on the FIFO.
 *
 * It is up to the caller to call `dif_flash_ctrl_status_get()` to ensure the
 * flash controller completed this transaction successfully.
 *
 * @param flash_ctrl flash controller device to push data to.
 * @param data The data to write.
 * @param word_count The number of words to write.
 * @param words_sent_out Out-parameter, the nuber of words written.
 * @return `kDifFlashCtrlProgBadArg` if `flash_ctrl`, `data`, or
 * `words_sent_out` is null, or if the value of `word_count` is illegal.
 * `kDifFlashCtrlProgInactive` if a program transaction was not started.
 * `kDifFlashCtrlProgFull` if the program FIFO fills up. `kDifFlashCtrlProgOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_prog_result_t dif_flash_ctrl_prog_fifo_push(
    dif_flash_ctrl_t *flash_ctrl, const uint32_t *data, uint32_t word_count,
    uint32_t *words_sent_out);

/**
 * Result type for operations on the read FIFO.
 */
typedef enum dif_flash_ctrl_read_result {
  /**
   * No error occurred.
   */
  kDifFlashCtrlReadOk = kDifFlashCtrlOk,
  /**
   * An unknown error occurred.
   *
   * @sa #kDifFlashCtrlError
   */
  kDifFlashCtrlReadError = kDifFlashCtrlError,
  /**
   * An invalid argument was provided.
   *
   * @sa #kDifFlashCtrlBadArg
   */
  kDifFlashCtrlReadBadArg = kDifFlashCtrlBadArg,
  /**
   * The read FIFO emptied before all data was read
   *
   * This error is recoverable by waiting for more data to be pushed to the read
   * FIFO.
   */
  kDifFlashCtrlReadEmpty,
} dif_flash_ctrl_read_result_t;

/**
 * Read data from the read FIFO.
 *
 * Attempts to read `word_count` words from the read FIFO.
 *
 * The following conditions are required:
 *   - `data_out` must reference a contiguous, allocated, writable region of at
 *     least `word_count` words, violation of this will produce undefined
 *     behavior.
 *   - The first call to this function after starting the program transaction
 *     the same `word_count` must not exceed what was supplied at the start of
 * the read transaction.
 *   - Each subsequent call the new `word_count` must not exceed `word_count -
 *     words_received_out` from the previous call.
 * All deviations on the above will produce a `kDifFlashCtrlReadBadArg` error
 * unless otherwise specified.
 *
 * If the FIFO empties this function may return `kDifFlashCtrlReadEmpty`
 * indicating that there is no available data to read from the FIFO and there is
 * still data pending. This function should be called again once more data
 * becomes available on the FIFO.
 *
 * It is up to the caller to call `dif_flash_ctrl_status_get()` to ensure the
 * flash controller completed this transaction successfully.
 *
 * @param flash_ctrl flash controller device to pull data from.
 * @param word_count The number of words to read.
 * @param data_out The region in memory to store the data read off the FIFO.
 * @param words_read_out Out-parameter, the number of words read.
 * @return `kDifFlashCtrlReadBadArg` if `flash_ctrl`, `data_out`, or
 * `words_read_out` is null, or if the value of `word_count` is illegal.
 * `kDifFlashCtrlReadEmpty` if the read FIFO fills up. `kDifFlashCtrlReadOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_read_result_t dif_flash_ctrl_read_fifo_pull(
    dif_flash_ctrl_t *flash_ctrl, uint32_t word_count, uint32_t *data_out,
    size_t *words_read_out);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus
#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_
