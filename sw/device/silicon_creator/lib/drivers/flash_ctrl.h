// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_

#include <limits.h>

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
typedef enum flash_ctrl_partition {
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
 * Table of flash information pages.
 *
 * Columns: Name, value, bank index, page index.
 * We use an X macro to faciliate writing enums, swtich statements, and unit
 * tests using the contants here. All information pages in this table are of
 * type 0 since silicon creator code does not need to access information pages
 * of other types.
 */
// clang-format off
#define FLASH_CTRL_INFO_PAGES_DEFINE(X) \
  /**
   * Bank 0 information partition type 0 pages.
   */ \
  X(kFlashCtrlInfoPageFactoryId,           0, 0) \
  X(kFlashCtrlInfoPageCreatorSecret,       0, 1) \
  X(kFlashCtrlInfoPageOwnerSecret,         0, 2) \
  X(kFlashCtrlInfoPageWaferAuthSecret,     0, 3) \
  X(kFlashCtrlInfoPageAttestationKeySeeds, 0, 4) \
  X(kFlashCtrlInfoPageBank0Type0Page5,     0, 5) \
  X(kFlashCtrlInfoPageOwnerReserved0,      0, 6) \
  X(kFlashCtrlInfoPageOwnerReserved1,      0, 7) \
  X(kFlashCtrlInfoPageOwnerReserved2,      0, 8) \
  X(kFlashCtrlInfoPageOwnerReserved3,      0, 9) \
  /**
   * Bank 1 information partition type 0 pages.
   */ \
  X(kFlashCtrlInfoPageBootData0,          1, 0) \
  X(kFlashCtrlInfoPageBootData1,          1, 1) \
  X(kFlashCtrlInfoPageOwnerSlot0,         1, 2) \
  X(kFlashCtrlInfoPageOwnerSlot1,         1, 3) \
  X(kFlashCtrlInfoPageBank1Type0Page4,    1, 4) \
  X(kFlashCtrlInfoPageBank1Type0Page5,    1, 5) \
  X(kFlashCtrlInfoPageCreatorCertificate, 1, 6) \
  X(kFlashCtrlInfoPageBootServices,       1, 7) \
  X(kFlashCtrlInfoPageOwnerCerificate0,   1, 8) \
  X(kFlashCtrlInfoPageOwnerCerificate1,   1, 9) \
// clang-format on

/**
 * A struct for storing base, config write-enable register, and config register
 * addresses of an info page.
 */
typedef struct flash_ctrl_info_page {
  /**
   * Base address.
   */
  uint32_t base_addr;
  /**
   * Config write-enable register address.
   */
  uint32_t cfg_wen_addr;
  /**
   * Config register address.
   */
  uint32_t cfg_addr;
} flash_ctrl_info_page_t;

/**
 * Helper macro for declaring an extern `flash_ctrl_info_page_t`.
 * @param name_ Name of the enumeration constant.
 * @param bank_ Bank of the info page.
 * @param page_ Page of the info page.
 */
#define INFO_PAGE_STRUCT_DECL_(name_, bank_, page_) \
  extern const flash_ctrl_info_page_t name_;

/**
 * Info pages.
 */
FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_DECL_);

#undef INFO_PAGE_STRUCT_DECL_

/**
 * Bitfields for `CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG` and
 * `CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG` OTP items.
 *
 * Defined here to be able to use in tests.
 */
#define FLASH_CTRL_OTP_FIELD_SCRAMBLING \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 0 }
#define FLASH_CTRL_OTP_FIELD_ECC \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 1 }
#define FLASH_CTRL_OTP_FIELD_HE \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 2 }

/**
 * Bitfields for `CREATOR_SW_CFG_FLASH_HW_INFO_CFG_OVERRIDE` OTP item.
 *
 * Defined here to be able to use in tests.
 */
#define FLASH_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_SCRAMBLE_DIS \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 0 }
#define FLASH_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_ECC_DIS \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 1 }

/**
 * The following constants represent the expected number of sec_mmio
 * register writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  flash_ctrl_init();
 *  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit);
 * ```
 */
enum {
  kFlashCtrlSecMmioCreatorInfoPagesLockdown = 16,
  kFlashCtrlSecMmioDataDefaultCfgSet = 1,
  kFlashCtrlSecMmioDataDefaultPermsSet = 1,
  kFlashCtrlSecMmioExecSet = 1,
  kFlashCtrlSecMmioInfoCfgSet = 1,
  kFlashCtrlSecMmioInfoPermsSet = 1,
  kFlashCtrlSecMmioBankErasePermsSet = 1,
  kFlashCtrlSecMmioInit = 3,
};

/**
 * Value of a word in flash after erase.
 */
enum {
  kFlashCtrlErasedWord = UINT32_MAX,
};

/**
 * Kicks off the initialization of the flash controller.
 *
 * This must complete before flash can be accessed. The init status can be
 * queried by calling `flash_ctrl_status_get()` and checking `init_wip`.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit)` when sec_mmio is being
 * used to check expectations.
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
 * @param[out] data Buffer to store the read data. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_data_read(uint32_t addr, uint32_t word_count,
                                 void *data);

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
 * @param[out] data Buffer to store the read data. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_info_read(const flash_ctrl_info_page_t *info_page,
                                 uint32_t offset, uint32_t word_count,
                                 void *data);

/**
 * Writes data to the data partition.
 *
 * The flash controller will truncate to the closest, lower word aligned
 * address. For example, if 0x13 is supplied, the controller will start writing
 * at address 0x10.
 *
 * @param addr Address to write to.
 * @param word_count Number of bus words to write.
 * @param data Data to write. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                  const void *data);

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
 * @param data Data to write. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_info_write(const flash_ctrl_info_page_t *info_page,
                                  uint32_t offset, uint32_t word_count,
                                  const void *data);

/*
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 2 -n 32 \
 *     -s 2181785819 --language=c
 *
 * Minimum Hamming distance: 14
 * Maximum Hamming distance: 14
 * Minimum Hamming weight: 14
 * Maximum Hamming weight: 18
 */

typedef enum flash_ctrl_erase_type {
  /**
   * Erase a page.
   */
  kFlashCtrlEraseTypePage = 0xaf0eab8b,
  /**
   * Erase a bank.
   */
  kFlashCtrlEraseTypeBank = 0x80329be9,
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
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_data_erase(uint32_t addr,
                                  flash_ctrl_erase_type_t erase_type);

/**
 * Verifies that a data partition page or bank was erased.
 *
 * @param addr Address that falls within the bank or page erased.
 * @param erase_type Whether to verify a page or a bank.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_data_erase_verify(uint32_t addr,
                                         flash_ctrl_erase_type_t erase_type);

/**
 * Erases an information partition page or bank.
 *
 * @param info_page Information page to erase for page erases, or a page within
 * the bank to erase for bank erases.
 * @param erase_type Whether to erase a page or a bank.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t flash_ctrl_info_erase(const flash_ctrl_info_page_t *info_page,
                                  flash_ctrl_erase_type_t erase_type);

/**
 * A struct for specifying access permissions.
 *
 * flash_ctrl config registers use 4-bits for boolean values. Use
 * `kMultiBitBool4True` to enable and `kMultiBitBool4False` to disable
 * permissions.
 */
typedef struct flash_ctrl_perms {
  /**
   * Read.
   */
  multi_bit_bool_t read;
  /**
   * Write.
   */
  multi_bit_bool_t write;
  /**
   * Erase.
   */
  multi_bit_bool_t erase;
} flash_ctrl_perms_t;

/**
 * Sets default access permissions for the data partition.
 *
 * A permission is enabled only if the corresponding field in `perms` is
 * `kMultiBitBool4True`.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioDataDefaultPermsSet)` when
 * sec_mmio is being used to check expectations.
 *
 * @param perms New permissions.
 */
void flash_ctrl_data_default_perms_set(flash_ctrl_perms_t perms);

/**
 * Sets access permissions for an info page.
 *
 * A permission is enabled only if the corresponding field in `perms` is
 * `kMultiBitBool4True`.
 *
 * * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInfoPermsSet)` when sec_mmio is
 * being used to check expectations.
 *
 * @param info_page An information page.
 * @param perms New permissions.
 */
void flash_ctrl_info_perms_set(const flash_ctrl_info_page_t *info_page,
                               flash_ctrl_perms_t perms);

/**
 * A struct for flash configuration settings.
 *
 * flash_ctrl config registers use 4-bits for boolean values. Use
 * `kMultiBitBool4True` to enable and `kMultiBitBool4False` to disable
 * these settings.
 *
 * This struct has no padding, so it is safe to `memcmp()` without invoking UB.
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

OT_ASSERT_MEMBER_OFFSET(flash_ctrl_cfg_t, scrambling, 0);
OT_ASSERT_MEMBER_OFFSET(flash_ctrl_cfg_t, ecc, 4);
OT_ASSERT_MEMBER_OFFSET(flash_ctrl_cfg_t, he, 8);
OT_ASSERT_SIZE(flash_ctrl_cfg_t, 12);

/**
 * Sets default configuration settings for the data partition.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioDataDefaultCfgSet)` when sec_mmio
 * is being used to check expectations.
 *
 * @param cfg New configuration settings.
 */
void flash_ctrl_data_default_cfg_set(flash_ctrl_cfg_t cfg);

/**
 * Reads the current default configuration settings for the data partition.
 *
 * @return Current configuration settings.
 */
flash_ctrl_cfg_t flash_ctrl_data_default_cfg_get(void);

/**
 * A type for flash_ctrl memory protection region indices.
 */
typedef uint32_t flash_ctrl_region_index_t;

/**
 * Configure memory protection for a region of pages.
 *
 * Based on the `region` parameter, this function overwrites the
 * `MP_REGION_${region}` and `MP_REGION_CFG_${region}` registers. Calling this
 * function invalidates previously-configured protections for `region`.
 *
 * @param region The index of the region to protect.
 * @param page_offset The index of the first page in the region.
 * @param num_pages The number of pages in the region.
 * @param perms The read/write/erase permissions for this region.
 * @param cfg Flash config values that are used to fill in some fields of the
 *            `MP_REGION_CFG_${region}` register.
 */
void flash_ctrl_data_region_protect(flash_ctrl_region_index_t region,
                                    uint32_t page_offset, uint32_t num_pages,
                                    flash_ctrl_perms_t perms,
                                    flash_ctrl_cfg_t cfg);

/**
 * Sets configuration settings for an info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInfoCfgSet)` when sec_mmio is
 * being used to check expectations.
 *
 * @param info_page An information page.
 * @param cfg New configuration settings.
 */
void flash_ctrl_info_cfg_set(const flash_ctrl_info_page_t *info_page,
                             flash_ctrl_cfg_t cfg);

/**
 * Set bank erase permissions for both flash banks.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioBankErasePermsSet)` when
 * sec_mmio is being used to check expectations.
 *
 * @param enable Whether to enable bank erase.
 */
void flash_ctrl_bank_erase_perms_set(hardened_bool_t enable);

/**
 * Enable execution from flash.
 *
 * Note: a ePMP region must also be configured in order to execute code in
 * flash.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioExecSet)` when sec_mmio is being
 * used to check expectations.
 *
 * @param exec_val Value to write to the `flash_ctrl.EXEC` register.
 * `FLASH_CTRL_PARAM_EXEC_EN` will enable execution, all other values will
 * disable execution.
 */
void flash_ctrl_exec_set(uint32_t exec_val);

/**
 * Disables all access to silicon creator info pages until next reset.
 *
 * This function must be called in ROM_EXT before handing over execution to the
 * first owner boot stage.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown)` when
 * sec_mmio is being used to check expectations.
 */
void flash_ctrl_creator_info_pages_lockdown(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_FLASH_CTRL_H_
