// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * A flash partition.
 *
 * Each `flash_ctrl_partition_t` enumeration constant is a bitfield with the
 * following layout:
 * - Bit 0: Data (0) or information (1) partition.
 * - Bits 1-2: Information partition type [0, 2].
 */
typedef enum flash_crtl_partition {
  /**
   * Data Partition.
   */
  kFlashCtrlPartitionData = 0,
  /**
   * Information partition of type 0.
   *
   * This partition has 10 pages.
   */
  kFlashCtrlPartitionInfo0 = (0 << 1) | 1,
  /**
   * Information partition of type 1.
   *
   * This partition has 1 page.
   */
  kFlashCtrlPartitionInfo1 = (1 << 1) | 1,
  /**
   * Information partition of type 2.
   *
   * This partition has 2 pages.
   */
  kFlashCtrlPartitionInfo2 = (2 << 1) | 1,
} flash_ctrl_partition_t;

/**
 * Bit and field definitions to get partition and info partition type from a
 * `flash_ctrl_partition_t`.
 */
#define FLASH_CTRL_PARTITION_BIT_IS_INFO 0
#define FLASH_CTRL_PARTITION_FIELD_INFO_TYPE \
  ((bitfield_field32_t){.mask = 0x3, .index = 1})

/**
 * Helper macro for defining the value of a `flash_ctrl_info_page_t` enumeration
 * constant for information pages of type 0.
 *
 * Each `flash_ctrl_info_page_t` enumeration constant is a bitfield with the
 * following layout:
 * - Bits 0-3: Page index ([0,9] for type 0, 0 for type 1, [0,1] for type 2).
 * - Bits 4-6: Partition type (a `flash_ctrl_partition_type_t`).
 * - Bit 7: Bank index [0,1].
 *
 * This macro assumes that all information pages are of type 0 since silicon
 * creator code does not need to access information pages of other types.
 *
 * @param bank_ Bank index.
 * @param page_ Page index.
 */
#define INFO_PAGE_(bank_, page_) \
  ((bank_ << 7) | (kFlashCtrlPartitionInfo0 << 4) | (page_))

// clang-format off
#define FLASH_CTRL_INFO_PAGES_DEFINE(X) \
  /**
   * Bank 0 information partition type 0 pages.
   */ \
  X(kFlashCtrlInfoPageFactoryId,          0, 0), \
  X(kFlashCtrlInfoPageCreatorSecret,      0, 1), \
  X(kFlashCtrlInfoPageOwnerSecret,        0, 2), \
  X(kFlashCtrlInfoPageWaferAuthSecret,    0, 3), \
  X(kFlashCtrlInfoPageBank0Type0Page4,    0, 4), \
  X(kFlashCtrlInfoPageBank0Type0Page5,    0, 5), \
  X(kFlashCtrlInfoPageOwnerReserved0,     0, 6), \
  X(kFlashCtrlInfoPageOwnerReserved1,     0, 7), \
  X(kFlashCtrlInfoPageOwnerReserved2,     0, 8), \
  X(kFlashCtrlInfoPageOwnerReserved3,     0, 9), \
  /**
   * Bank 1 information partition type 0 pages.
   */ \
  X(kFlashCtrlInfoPageBootData0,          1, 0), \
  X(kFlashCtrlInfoPageBootData1,          1, 1), \
  X(kFlashCtrlInfoPageOwnerSlot0,         1, 2), \
  X(kFlashCtrlInfoPageOwnerSlot1,         1, 3), \
  X(kFlashCtrlInfoPageBank1Type0Page4,    1, 4), \
  X(kFlashCtrlInfoPageBank1Type0Page5,    1, 5), \
  X(kFlashCtrlInfoPageCreatorCertificate, 1, 6), \
  X(kFlashCtrlInfoPageBootServices,       1, 7), \
  X(kFlashCtrlInfoPageOwnerCerificate0,   1, 8), \
  X(kFlashCtrlInfoPageOwnerCerificate1,   1, 9), \
// clang-format on

/**
 * Helper macro for defining a `flash_ctrl_info_page_t` enumeration constant.
 * @name_ Name of the enumeration constant.
 * @value_ Value of the enumeration constant.
 */
#define INFO_PAGE_ENUM_INIT_(name_, bank_, page_) name_ = INFO_PAGE_(bank_, page_)

/**
 * Info pages.
 */
typedef enum flash_ctrl_info_page {
  FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_ENUM_INIT_)
} flash_ctrl_info_page_t;

/**
 * Field and bit definitions to get page index, partition type, and bank index
 * from a `flash_ctrl_info_page_t`.
 */
#define FLASH_CTRL_INFO_PAGE_FIELD_PAGE \
  ((bitfield_field32_t){.mask = 0xf, .index = 0})
#define FLASH_CTRL_INFO_PAGE_FIELD_PARTITION \
  ((bitfield_field32_t){.mask = 0x7, .index = 4})
#define FLASH_CTRL_INFO_PAGE_BIT_BANK 7

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
 * Reads data from the data partition.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will perform a read
 * at address 0x10.
 *
 * @param addr Address to read from.
 * @param word_count Number of bus words to read.
 * @param[out] data Buffer to store the read data.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_data_read(uint32_t addr, uint32_t word_count,
                                 uint32_t *data);

/**
 * Reads data from an information page.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will start reading
 * at address 0x10.
 *
 * @param info_page Information page to read from.
 * @param offset Offset from the start of the page.
 * @param word_count Number of bus words to read.
 * @param[out] data Buffer to store the read data.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_info_read(flash_ctrl_info_page_t info_page,
                                 uint32_t offset, uint32_t word_count,
                                 uint32_t *data);

/**
 * Writes data to the data partition.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will start writing
 * at address 0x10.
 *
 * @param addr Address to write to.
 * @param word_count Number of bus words to write.
 * @param data Data to write.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                  const uint32_t *data);

/**
 * Writes data to an information page.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will start writing
 * at address 0x10.
 *
 * @param info_page Information page to write to.
 * @param offset Offset from the start of the page.
 * @param word_count Number of bus words to write.
 * @param data Data to write.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_info_write(flash_ctrl_info_page_t info_page,
                                  uint32_t offset, uint32_t word_count,
                                  const uint32_t *data);

typedef enum flash_ctrl_erase_type {
  /**
   * Erase a page.
   */
  kFlashCtrlEraseTypePage = 0,
  /**
   * Erase a bank.
   */
  kFlashCtrlEraseTypeBank = 1,
} flash_ctrl_erase_type_t;

/**
 * Erases a data partition page or bank.
 *
 * The flash controller will truncate to the closest page boundary for page
 * erase operations, and to the nearest bank aligned boundary for bank erase
 * operations.
 *
 * @param addr Address that falls within the bank or page being deleted.
 * @param erase_type Whether to erase a page or a bank.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_data_erase(uint32_t addr,
                                  flash_ctrl_erase_type_t erase_type);

/**
 * Erases an information partition page or bank.
 *
 * @param info_page Information page to erase for page erases, or a page within
 * the bank to erase for bank erases.
 * @param erase_type Whether to erase a page or a bank.
 * @return Result of the operation.
 */
rom_error_t flash_ctrl_info_erase(flash_ctrl_info_page_t info_page,
                                  flash_ctrl_erase_type_t erase_type);

/**
 * A struct for specifying access permissions.
 */
typedef struct flash_ctrl_perms {
  /**
   * Read.
   */
  hardened_bool_t read;
  /**
   * Write.
   */
  hardened_bool_t write;
  /**
   * Erase.
   */
  hardened_bool_t erase;
} flash_ctrl_perms_t;

/**
 * Sets default access permissions for the data partition.
 *
 * A permission is enabled only if the corresponding field in `perms` is
 * `kHardenedBoolTrue`.
 *
 * @param perms New permissions.
 */
void flash_ctrl_data_default_perms_set(flash_ctrl_perms_t perms);

/**
 * Sets access permissions for an info page.
 *
 * A permission is enabled only if the corresponding field in `perms` is
 * `kHardenedBoolTrue`.
 *
 * @param info_page An information page.
 * @param perms New permissions.
 */
void flash_ctrl_info_perms_set(flash_ctrl_info_page_t info_page,
                            flash_ctrl_perms_t perms);

/**
 * A struct for flash configuration settings.
 */
typedef struct flash_ctrl_cfg {
  /**
   * Scrambling.
   */
  multi_bit_bool_t scrambling;
  /**
   * ECC.
   */
  multi_bit_bool_t ecc;
  /**
   * High endurance.
   */
  multi_bit_bool_t he;
} flash_ctrl_cfg_t;

/**
 * Sets default configuration settings for the data partition.
 *
 * @param cfg New configuration settings.
 */
void flash_ctrl_data_default_cfg_set(flash_ctrl_cfg_t cfg);

/**
 * Sets configuration settings for an info page.
 *
 * @param info_page An information page.
 * @param cfg New configuration settings.
 */
void flash_ctrl_info_cfg_set(flash_ctrl_info_page_t info_page, flash_ctrl_cfg_t cfg);

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

/**
 * Disables all access to silicon creator info pages until next reset.
 *
 * This function must be called in ROM_EXT before handing over execution to the
 * first owner boot stage.
 */
void flash_ctrl_creator_info_pages_lockdown(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
