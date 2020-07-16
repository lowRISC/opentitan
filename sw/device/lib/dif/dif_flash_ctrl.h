// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 1.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/flash_ctrl/doc/">FLASH CTRL</a> Device Interface
 * Functions
 */

#ifdef __cplusplus
extern "C" {
#endif

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

/**
 * Configuration for initializing the FLASH CTRL device.
 */
typedef struct dif_flash_ctrl_config {
  //! The base address for registers in the FLASH CTRL IP.
  mmio_region_t base_addr;
} dif_flash_ctrl_config_t;

/**
 * Carries state for a FLASH CTRL device.
 *
 * All members should be considered private and should not be accessed directly
 * outside of the dif implementation. This struct is only public for allocation
 * purposes.
 */
typedef struct dif_flash_ctrl {
  //! The base address for registers in the FLASH CTRL IP.
  mmio_region_t base_addr;
} dif_flash_ctrl_t;

/**
 * Partition selection enumeration.
 */
typedef enum dif_flash_ctrl_part_sel {
  //! Select the data partition.
  kDifFlashCtrlPartSelData = 0,
  //! Select the info partition.
  kDifFlashCtrlPartSelInfo,
} dif_flash_ctrl_part_sel_t;

/**
 * Erase operation mode enumeration.
 */
typedef enum dif_flash_ctrl_erase_sel {
  //! Erase 1 page of flash.
  kDifFlashCtrlEraseSelPage,
  //! Erase 1 bank of flash.
  kDifFlashCtrlEraseSelBank,
} dif_flash_ctrl_erase_sel_t;

/**
 * Region access types enumeration.
 */
typedef enum dif_flash_ctrl_access {
  //! Read access.
  kDifFlashCtrlAccessRead,
  //! Program access.
  kDifFlashCtrlAccessProgram,
  //! Erase access.
  kDifFlashCtrlAccessErase,
} dif_flash_ctrl_access_t;

/**
 * Generic enable/disable enumeration.
 */
typedef enum dif_flash_ctrl_enable {
  //! Generic enable.
  kDifFlashCtrlEnable = 0,
  //! Generic disable.
  kDifFlashCtrlDisable,
} dif_flash_ctrl_enable_t;

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
  kDifFlashCtrlIrqOpError,
} dif_flash_ctrl_irq_t;

/**
 * Base result type for functions that may produce generic errors.
 */
typedef enum dif_flash_ctrl_result {
  //! No error occurred.
  kDifFlashCtrlOk = 0,
  //! An unknown error occurred.
  /*!
    This error is not recoverable.
  */
  kDifFlashCtrlError,
  //! An invalid argument was provided.
  /*!
    This error is recoverable and indicates the function produced no side
    effects.

    In order to recover from this error the caller must be aware of the
    possibility of passing invalid arguments and correct these arguments in
    future calls.
  */
  kDifFlashCtrlBadArg,
} dif_flash_ctrl_result_t;

/**
 * Result type for configuration transactions that may fail if FLASH CTRL is in
 * an invalid state.
 */
typedef enum dif_flash_ctrl_start_result {
  //! No error occurred.
  kDifFlashCtrlStartOk = 0,
  //! An unknown error occurred.
  /*!
    @sa #kDifFlashCtrlError
  */
  kDifFlashCtrlStartError,
  //! An invalid argument was provided.
  /*!
    @sa #kDifFlashCtrlBadArg
  */
  kDifFlashCtrlStartBadArg,
  //! A flash operation is in progress.
  /*!
    This error is recoverable and indicates the function produced no side
    effects.

    When a flash operation is in progress the control register cannot be
    updated. This error can be recovered from by waiting for the flash operation
    to complete.
  */
  kDifFlashCtrlStartBusy,
} dif_flash_ctrl_start_result_t;

/**
 * Result type for memory protection configuration actions.
 */
typedef enum dif_flash_ctrl_region_result {
  //! No error occurred.
  kDifFlashCtrlRegionOk = 0,
  //! An unknown error occurred.
  /*!
    @sa #kDifFlashCtrlError
  */
  kDifFlashCtrlRegionError,
  //! An invalid argument was provided.
  /*!
    @sa #kDifFlashCtrlBadArg
  */
  kDifFlashCtrlRegionBadArg,
  //! Region cannot be configured.
  /*!
    This error indicates the function produced no side effects.

    Once the flash region configuration registers have been locked they can't be
    written to until the next reset. A function that produces this error will
    continue producing errors on all subsequent calls until the device is reset.
  */
  kDifFlashCtrlRegionBadAccess,
} dif_flash_ctrl_region_result_t;

/**
 * Result type for bank configuration actions.
 */
typedef enum dif_flash_ctrl_bank_result {
  //! No error occurred.
  kDifFlashCtrlBankOk = 0,
  //! An unknown error occurred.
  /*!
    @sa #kDifFlashCtrlError
  */
  kDifFlashCtrlBankError,
  //! An invalid argument was provided.
  /*!
    @sa #kDifFlashCtrlBadArg
  */
  kDifFlashCtrlBankBadArg,
  //! Region cannot be configured.
  /*!
    This error indicates the function produced no side effects.

    Once bank configuration has been locked the associated registers cannot be
    written to until the next reset. A function that produces this error will
    continue producing errors on all subsequent calls until the device is reset.
  */
  kDifFlashCtrlBankLocked,
} dif_flash_ctrl_bank_result_t;

/**
 * Result type for operations on the program FIFO.
 */
typedef enum dif_flash_ctrl_prog_result {
  //! No error occurred.
  kDifFlashCtrlProgOk = 0,
  //! An unknown error occurred.
  /*!
    @sa #kDifFlashCtrlError
  */
  kDifFlashCtrlProgError,
  //! An invalid argument was provided.
  /*!
    @sa #kDifFlashCtrlBadArg
  */
  kDifFlashCtrlProgBadArg,
  //! A program operation was not initiated.
  /*!
    This error is recoverable and indicates the function produced no side
    effects.

    Before writing to the program FIFO a program operation must first be
    started. This can be recovered with a call to `dif_flash_ctrl_prog_start()`.
  */
  kDifFlashCtrlProgInactive,
  //! The program FIFO filled up.
  /*!
    This error is recoverable by waiting for space to free up on the program
    FIFO.
  */
  kDifFlashCtrlProgFull,
} dif_flash_ctrl_prog_result_t;

/**
 * Result type for operations on the read FIFO.
 */
typedef enum dif_flash_ctrl_read_result {
  //! No error occurred.
  kDifFlashCtrlReadOk = 0,
  //! An unknown error occurred.
  /*!
    @sa #kDifFlashCtrlError
  */
  kDifFlashCtrlReadError,
  //! An invalid argument was provided.
  /*!
    @sa #kDifFlashCtrlBadArg
  */
  kDifFlashCtrlReadBadArg,
  //! The read FIFO emptied before all data was read
  /*!
    This error is recoverable by waiting for more data to be pushed to the read
    FIFO.
  */
  kDifFlashCtrlReadEmpty,
} dif_flash_ctrl_read_result_t;
/**
 * Initializes the FLASH CTRL device described by `config`, writing internal
 * state to `flash_ctrl_out`.
 *
 * This function must be called to obtain a valid `dif_flash_ctrl_t` for use in
 * all other functions of this dif.
 *
 * @param config Configuration for this FLASH CTRL device.
 * @param flash_ctrl_out An out-parameter to hold internal FLASH CTRL state.
 *
 * @return `kDifFlashCtrlBadArg` if `config` is null or contains illegal
 * arguments or if `flash_ctrl_out` is null, `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_init(
    const dif_flash_ctrl_config_t *config, dif_flash_ctrl_t *flash_ctrl_out);

/**
 * FLASH CTRL get requested IRQ state.
 *
 * Get the state of the requested IRQ in `irq_type`.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param irq_type IRQ to get the state of.
 * @param state IRQ state passed back to the caller.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t *state);
/**
 * FLASH CTRL clear requested IRQ state.
 *
 * Clear the state of the requested IRQ in `irq_type`. Primary use of this
 * function is to de-assert the interrupt after it has been serviced.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param irq_type IRQ to be de-asserted.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_state_clear(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type);

/**
 * FLASH CTRL disable interrupts.
 *
 * Disable generation of all FLASH CTRL interrupts, and pass previous interrupt
 * state in `state` back to the caller. Parameter `state` is ignored if NULL.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param state IRQ state passed back to the caller.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irqs_disable(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t *state);

/**
 * FLASH CTRL restore IRQ state.
 *
 * Restore previous FLASH CTRL IRQ state. This function is used to restore the
 * FLASH CTRL interrupt state prior to `dif_flash_ctrl_irqs_disable` function
 * call.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param state IRQ state to restore.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irqs_restore(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t state);

/**
 * FLASH CTRL interrupt control.
 *
 * Enable/disable an FLASH CTRL interrupt specified in `enable`.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param irq_type FLASH CTRL interrupt type.
 * @param enable enable or disable the interrupt.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_control(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type,
    dif_flash_ctrl_enable_t enable);

/**
 * FLASH CTRL interrupt force.
 *
 * Force interrupt specified in `irq_type`.
 *
 * @param flash_ctrl FLASH CTRL state data.
 * @param irq_type FLASH CTRL interrupt type to be forced.
 * @return `dif_flash_ctrl_result_t`.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_irq_force(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_irq_t irq_type);

/**
 * Set the partition to operate on for following transactions.
 *
 * @param flash_ctrl FLASH CTRL device to set the partition for.
 * @param part The partition to set as active.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_partition_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_part_sel_t part);

/**
 * Get the active partition that transactions will operate on.
 *
 * @param flash_ctrl FLASH CTRL device to set the partition for.
 * @param part_out Out-parameter, the active partition.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `part_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_partition_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_part_sel_t *part_out);

/**
 * Set the scramble mode for the following transactions.
 *
 * The scramble mode for a region must be the same for reads and writes
 * otherwise the data read will be "scrambled" garbage.
 *
 * @param flash_ctrl FLASH CTRL device to set scrambling for.
 * @param enable The mode to set, either enable or disable scrambling.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_scramble_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t enable);

/**
 * Get the scramble current mode.
 *
 * @param flash_ctrl FLASH CTRL device to get the scrambling mode of.
 * @param enable_out Out-parameter, the current scramble mode.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` `or enable_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_result_t dif_flash_ctrl_scramble_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t *enable_out);

//TODO document how address is resolved in the next three operations.
/**
 * Start a read transaciton.
 *
 * @param flash_ctrl FLASH CTRL device to execute the transaciton on.
 * @param addr The address to read.
 * @param word_count The number of bus words the flash operation should read.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_read_start(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count);

/**
 * Start a program transaciton.
 *
 * @param flash_ctrl FLASH CTRL device to execute the transaciton on.
 * @param addr The address to program.
 * @param word_count The number of bus words the flash operation should program.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_prog_start(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr, uint32_t word_count);

/**
 * Start an erase transaciton.
 *
 * @param flash_ctrl FLASH CTRL device to execute the transaciton on.
 * @param addr The address to read.
 * @param erase_sel The erase mode.
 * @return `kDifFlashCtrlStartBadArg` if `flash_ctrl` is null,
 * `kDifFlashCtrlStartBusy` if a flash transaction is in progress, and
 * `kDifFlashCtrlStartOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_start_result_t dif_flash_ctrl_erase_start(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t addr,
    dif_flash_ctrl_erase_sel_t erase_sel);

/**
 * Enable/disable the region of flash indexed by `region`.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param region The region to operate on.
 * @param enable Enable or disable this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
DIF_WARN_UNUSED_RESULT
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_enable_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the enabled/disabled state for this region.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param region The region in question.
 * @param enable_out Out-parameter, the enabled/disabled state of this region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_enable_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Set access permissions for the region of flash indexed by `region`.
 *
 * Read, program, and erase permissions can be enabled/disabled depending on the
 * values of `access` and `enable`.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param region The region to operate on.
 * @param access The access type to control for this `region`.
 * @param enable Enable or disable `access` type transactions on this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_access_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_access_t access, dif_flash_ctrl_enable_t enable);

/**
 * Get the access permissions for this region.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param region The region in question.
 * @param access The access type to query for this `region`.
 * @param enable_out Out-parameter, the enabled/disabled state of `access` type
 * transactions on this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_access_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_access_t access, dif_flash_ctrl_enable_t *enable_out);

/**
 * Set access permissions for the default region.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param access The access type to control for this `region`.
 * @param enable Enable or disable `access` type transactions on the default
 * region.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
dif_flash_ctrl_region_result_t dif_flash_ctrl_default_access_set(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_access_t access,
    dif_flash_ctrl_enable_t enable);

/**
 * Get the access permissions for the default region.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param access The access type to query for this `region`.
 * @param enable_out Out-parameter, the enabled/disabled state of `access` type
 * transactions for the default region.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_default_access_get(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_access_t access,
    dif_flash_ctrl_enable_t *enable_out);

/**
 * Set the base page for this region.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param region The region to operate on.
 * @param page The starting page for this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_base_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t page);

/**
 * Get the base page for this region.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param region The region in question.
 * @param page_out Out-parameter, the base page for this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_base_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *page_out);

/**
 * Set the size of this region in number of pages.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param region The region to operate on.
 * @param size The `region` size in number of pages.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_size_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t size);

/**
 * Get the size of this region in number of pages.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param region The region in question.
 * @param size_out Out-parameter, the number of pages in this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_size_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region, uint32_t *size_out);

/**
 * Set the partition for this region.
 *
 * This may only be done if region configuration has not been locked.
 *
 * @param flash_ctrl FLASH CTRL device to configure.
 * @param region The region to operate on.
 * @param part The partition to set for this `region`.
 * @return `kDifFlashCtrlRegionBadArg` if `flash_ctrl` is null or `region` is
 * invalid, `kDifFlashCtrlRegionBadAccess` if region configuration has been
 * locked, and `kDifFlashCtrlRegionOk` otherwise.
 */
dif_flash_ctrl_region_result_t dif_flash_ctrl_region_partition_set(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_part_sel_t part);

/**
 * Get the partition this region refers to.
 *
 * @param flash_ctrl FLASH CTRL device to query.
 * @param region The region in question.
 * @param part_out Out-parameter, the active partition for this `region`.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `enable_out` is null, or if
 * `region` is invalid, `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_partition_get(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t region,
    dif_flash_ctrl_part_sel_t *part_out);

/**
 * Lock memory region configuration until the device is reset.
 *
 * This will prevent any further configuration of memory regions until device
 * reset. Future calls to region configuration functions will return
 * `kDifFlashCtrlRegionBadAccess`.
 *
 * @param flash_ctrl FLASH CTRL device to lock region configuration on.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_regions_config_disable(
    const dif_flash_ctrl_t *flash_ctrl);

/**
 * Query the state of the memory region configuration registers.
 *
 * This function checks if memory region configuration is still enabled or if
 * has been locked. Once locked, region configuration cannot be enabled again,
 * and all calls to region configuration functions will return
 * `kDifFlashCtrlRegionBadAccess` until the device is restarted.
 *
 * @param flash_ctrl FLASH CTRL device to check the lock state for.
 * @param access_out Out-parameter, the current state of memory region
 * configuration access.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `access_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_region_config_check(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t *access_out);

/**
 * Erase an entire bank of flash.
 *
 * This may only be done if bank configuration is still enabled.
 *
 * @param flash_ctrl FLASH CTRL device to operate on.
 * @param bank The bank to clear.
 * @return `kDifFlashCtrlBankBadArg` if `flash_ctrl` is null or `bank` is
 * invalid, `kDifFlashCtrlBankBadAccess` if bank configuration is locked, and
 * `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_bank_result_t dif_flash_ctrl_bank_erase(
    const dif_flash_ctrl_t *flash_ctrl, uint32_t bank);

/**
 * Lock bank configuration until the device is reset.
 *
 * This will prevent any further configuration of memory banks until device
 * reset. Future calls to bank configuration functions will return
 * `kDifFlashCtrlBankBadAccess`.
 *
 * @param flash_ctrl FLASH CTRL device to lock region configuration on.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_disable(
    const dif_flash_ctrl_t *flash_ctrl);

/**
 * Query the state of the bank configuration registers.
 *
 * This function checks if memory bank configuration is still enabled or if
 * has been locked. Once locked, bank configuration cannot be enabled again,
 * and all calls to bank configuration functions will return
 * `kDifFlashCtrlBankBadAccess` until the device is restarted.
 *
 * @param flash_ctrl FLASH CTRL device to check the lock state for.
 * @param access_out Out-parameter, the current state of bank configuration
 * access.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` or `access_out` is null,
 * `kDifFlashCtrlOk` otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_bank_config_check(
    const dif_flash_ctrl_t *flash_ctrl, dif_flash_ctrl_enable_t *access_out);

/**
 * Resets both the program and read FIFOs.
 *
 * This is useful in the event of an unexpected error as a means of reseting
 * state.
 *
 * @param flash_ctrl FLASH CTRL device to clear FIFOs on.
 * @return `kDifFlashCtrlBadArg` if `flash_ctrl` is null, `kDifFlashCtrlOk`
 * otherwise.
 */
dif_flash_ctrl_result_t dif_flash_ctrl_fifo_reset(
    const dif_flash_ctrl_t *flash_ctrl);

/**
 * Push data to the program FIFO.
 *
 * Attempts to write the contents of `data` to the program FIFO. It is required
 * that a program transaction be started prior to calling this function, else
 * the call will fail with `kDifFlashCtrlProgInactive`.
 *
 * The following conditions are also required:
 *   - `data` must reference a contiguous, allocated, readable region of at
 *     least `len` bytes, violation of this will produce undefined behavior.
 *   - `data` must be word aligned. TODO is this an okay restriction?
 *   - `len` must be divisible by the bus word size.
 *   - The first call to this function after starting the program transaction
 *     `len / WORD_SIZE == word_count`, the same `word_count` supplied at the
 *     start of the program transaction.
 *   - Each subsequent call the new `len` must equal `len - *bytes_sent_out`
 *     from the previous call.
 * All deviations on the above will produce a `kDifFlashCtrlProgBadArg` error
 * unless otherwise specified.
 *
 * If the FIFO fills up this function may return `kDifFlashCtrlProgFull`
 * indicating that not all data was written and this function must be called
 * again once space has freed up on the FIFO.
 *
 * @param flash_ctrl FLASH CTRL device to push data to.
 * @param data The data to write.
 * @param len The number of bytes to write.
 * @param bytes_sent_out Out-parameter, the number of bytes sent.
 * @return `kDifFlashCtrlProgBadArg` if `flash_ctrl`, `data`, or
 * `bytes_sent_out` is null, or if `data` or `len` have illegal values.
 * `kDifFlashCtrlProgInactive` if a program transaction was not started.
 * `kDifFlashCtrlProgFull` if the program FIFO fills up. `kDifFlashCtrlProgOk`
 * otherwise.
 */
dif_flash_ctrl_prog_result_t dif_flash_ctrl_prog_fifo_push(
    const dif_flash_ctrl_t *flash_ctrl, size_t len, const void *data,
    size_t *bytes_sent_out);

/**
 * Read data from the read FIFO.
 *
 * Attempts to read `len` bytes from the read FIFO.
 *
 * The following conditions are required:
 *   - `data_out` must reference a contiguous, allocated, writable region of at
 *     least `len` bytes, violation of this will produce undefined behavior.
 *   - `data_out` must be word aligned. TODO is this an okay restriction?
 *   - `len` must be divisible by the bus word size.
 *   - The first call to this function after starting the read transaction
 *     `len / WORD_SIZE == word_count`, the same `word_count` supplied at the
 *     start of the read transaction.
 *   - Each subsequent call the new `len` must equal `len - *bytes_read_out`
 *     from the previous call.
 * All deviations on the above will produce a `kDifFlashCtrlReadBadArg` error
 * unless otherwise specified.
 *
 * If the FIFO empties this function may return `kDifFlashCtrlReadEmpty`
 * indicating that there is no available data to read from the FIFO and there is
 * still data pending. This function should be called again once more data
 * becomes available on the FIFO.
 *
 * @param flash_ctrl FLASH CTRL device to pull data from.
 * @param len The number of bytes to read.
 * @param data_out The region in memory to store the data read off the FIFO.
 * @param bytes_read_out Out-parameter, the number of bytes read.
 * @return `kDifFlashCtrlReadBadArg` if `flash_ctrl`, `data_out`, or
 * `bytes_read_out` is null, or if `data_out` or `len` have illegal values.
 * `kDifFlashCtrlReadEmpty` if the read FIFO fills up. `kDifFlashCtrlReadOk`
 * otherwise.
 */
dif_flash_ctrl_read_result_t dif_flash_ctrl_read_fifo_pull(
    const dif_flash_ctrl_t *flash_ctrl, size_t len, void *data_out,
    size_t *bytes_read_out);


#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_FLASH_CTRL_H_

