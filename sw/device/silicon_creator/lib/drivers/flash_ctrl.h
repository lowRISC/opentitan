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
} flash_ctrl_status_t;

/**
 * Query the status registers on the flash controller.
 *
 * This function checks the various status bits as described in
 * `flash_ctrl_status_t`.
 *
 * @param flash_ctrl flash controller device to check the status bits for.
 * @param[out] status_out The current status of the flash controller.
 * @return `kErrorFlashCtrlInvalidArgument` if `status` is NULL, `kErrorOk`
 * otherwise.
 */
rom_error_t flash_ctrl_status_get(flash_ctrl_status_t *status);

/**
 * Region selection enumeration. Represents both the partition and the info
 * type.
 */
typedef enum flash_crtl_partition {
  /**
   * Select the data partition.
   */
  kFlashCtrlRegionData = 0x0000,
  /**
   * Select the info partition of type 0.
   */
  kFlashCtrlRegionInfo0 = 0x0100,
  /**
   * Select the info partition of type 1.
   */
  kFlashCtrlRegionInfo1 = 0x0300,
  /**
   * Select the info partition of type 2.
   */
  kFlashCtrlRegionInfo2 = 0x0500,
} flash_ctrl_partition_t;

/**
 * Start a read transaction.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will perform a read
 * at address 0x10.
 *
 * @param addr The address to read from.
 * @param word_count The number of bus words the flash operation should read.
 * @param region The region to read from.
 * @return `kErrorFlashCtrlBusy` if the flash controller is already processing a
 * transaction, `kErrorOk` otherwise.
 */
rom_error_t flash_ctrl_read_start(uint32_t addr, uint32_t word_count,
                                  flash_ctrl_partition_t region);

/**
 * Read data from the read FIFO.
 *
 * Attempts to read `word_count` words from the read FIFO.
 *
 * It is up to the caller to call `flash_ctrl_status_get()` to ensure the
 * flash controller completed this transaction successfully.
 *
 * @param word_count The number of words to read.
 * @param data_out The region in memory to store the data read off the FIFO.
 * @return The number of words read from the FIFO.
 */
size_t flash_ctrl_fifo_read(size_t word_count, uint32_t *data_out);

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
