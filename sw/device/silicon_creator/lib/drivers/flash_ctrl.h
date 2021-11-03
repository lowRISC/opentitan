// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_

#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Kicks of the initialization of the flash controller.
 *
 * This must complete before flash can be accessed. The init status can be
 * queried by calling `flash_ctrl_status_get()` and checking `init_wip`.
 */
void flash_ctrl_init(void);

/**
 * Status bits.
 */
typedef struct flash_ctrl_status {
  /**
   * Flash read FIFO full, software must consume data.
   */
  bool rd_full;
  /**
   * Flash read FIFO empty.
   */
  bool rd_empty;
  /**
   * Flash program FIFO full, software must consume data.
   */
  bool prog_full;
  /**
   * Flash program FIFO empty.
   */
  bool prog_empty;
  /**
   * Flash controller undergoing init.
   */
  bool init_wip;
} flash_ctrl_status_t;

/**
 * Query the status registers on the flash controller.
 *
 * This function checks the various status bits as described in
 * `flash_ctrl_status_t`.
 *
 * @param flash_ctrl flash controller device to check the status bits for.
 * @param[out] status_out The current status of the flash controller.
 */
void flash_ctrl_status_get(flash_ctrl_status_t *status);

/**
 * Region selection enumeration. Represents both the partition and the info
 * type.
 */
typedef enum flash_crtl_partition {
  /**
   * Select the data partition.
   */
  kFlashCtrlPartitionData = 0x0000,
  /**
   * Select the info partition of type 0.
   */
  kFlashCtrlPartitionInfo0 = 0x0100,
  /**
   * Select the info partition of type 1.
   */
  kFlashCtrlPartitionInfo1 = 0x0300,
  /**
   * Select the info partition of type 2.
   */
  kFlashCtrlPartitionInfo2 = 0x0500,
} flash_ctrl_partition_t;

/**
 * Perform a read transaction.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will perform a read
 * at address 0x10.
 *
 * On success, `data` is populated with the read data.
 *
 * For operations that fail with `kErrorFlashCtrlInternal`, `err` is set to the
 * internal error mask for flash_ctrl, which can be checked against the
 * `kFlashCtrlErr*` bits. The internal error state is cleared after each call.
 *
 * @param addr The address to read from.
 * @param word_count The number of bus words the flash operation should read.
 * @param region The region to read from.
 * @param[out] data The buffer to store the read data.
 * @param[out] err The internal error state of flash_ctrl.
 * @return `kErrorFlashCtrlBusy` if the flash controller is already processing a
 * transaction, `kErrorFlashCtrlInternal` if the operations fails, `kErrorOk`
 * otherwise.
 */
rom_error_t flash_ctrl_read(uint32_t addr, uint32_t word_count,
                            flash_ctrl_partition_t partition, uint32_t *data);

/**
 * Perform a program transaction.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will start writing
 * at address 0x10.
 *
 * For operations that fail with `kErrorFlashCtrlInternal`, `err` is set to the
 * internal error mask for flash_ctrl, which can be checked against the
 * `kFlashCtrlErr*` bits. The internal error state is cleared after each call.
 *
 * @param addr The address to write to.
 * @param word_count The number of bus words the flash operation should program.
 * @param region The region to program.
 * @param data The buffer containing the data to program to flash.
 * @param[out] err The internal error state of flash_ctrl.
 * @return `kErrorFlashCtrlBusy` if the flash controller is already processing a
 * transaction, `kErrorFlashCtrlInternal` if the operations fails, `kErrorOk`
 * otherwise.
 */
rom_error_t flash_ctrl_prog(uint32_t addr, uint32_t word_count,
                            flash_ctrl_partition_t partition,
                            const uint32_t *data);

typedef enum flash_ctrl_erase_type {
  /**
   * Erase a page.
   */
  kFlashCtrlEraseTypePage = 0x0000,
  /**
   * Erase a bank.
   */
  kFlashCtrlEraseTypeBank = 0x0080,
} flash_ctrl_erase_type_t;

/**
 * Invoke a blocking erase transaction.
 *
 * The flash controller will truncate to the closest page boundary for page
 * erase operations, and to the nearest bank aligned boundary for bank erase
 * operations.
 *
 * For operations that fail with `kErrorFlashCtrlInternal`, `err` is set to the
 * internal error mask for flash_ctrl, which can be checked against the
 * `kFlashCtrlErr*` bits. The internal error state is cleared after each call.
 *
 * @param addr The address that falls within the bank or page being deleted.
 * @param region The region that contains the bank or page being deleted.
 * @param[out] err The internal error state of flash_ctrl.
 * @return `kErrorFlashCtrlBusy` if the flash controller is already processing a
 * transaction, `kErrorFlashCtrlInternal` if the operations fails, `kErrorOk`
 * otherwise.
 */
rom_error_t flash_ctrl_erase(uint32_t addr, flash_ctrl_partition_t partition,
                             flash_ctrl_erase_type_t erase_type);

typedef enum flash_ctrl_exec {
  kFlashCtrlExecDisable = kMultiBitBool4False,
  kFlashCtrlExecEnable = kMultiBitBool4True,
} flash_ctrl_exec_t;

/**
 * Enable execution from flash.
 *
 * Note: a ePMP region must also be configured in order to execute code in
 * flash.
 *
 * @param `enable` Value to write to the `flash_ctrl.EXEC` register. The
 *                value `0xa` will enable execution, all other values will
 *                disable execution.
 */
void flash_ctrl_exec_set(flash_ctrl_exec_t enable);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
