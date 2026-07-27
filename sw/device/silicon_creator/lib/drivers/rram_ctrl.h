// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RRAM_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RRAM_CTRL_H_

#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * A logical RRAM info page.
 *
 * Unlike flash, RRAM has only `RRAM_CTRL_PARAM_NUM_INFO_PAGES` (8) physical
 * info pages, too few for the 20 logical pages named in `nvm_info_page_t`.
 * The 6 most security-sensitive pages (including the ones
 * `nvm_ctrl_creator_info_pages_lockdown()` must revoke creator access to) get
 * a real, individually-protected info page (`emulated` = false). The
 * remaining 14 are "emulated": relocated onto reserved pages of the (much
 * larger) RRAM data partition, all sharing a single memory-protection region
 * with permissions that can't be restricted per-page.
 *
 * TODO(#XXXX): because 3 of the 7 pages `nvm_ctrl_creator_info_pages_lockdown`
 * must revoke (`BootData0`, `BootData1`, `CreatorReserved0`) are emulated and
 * share a region with owner-needed pages (`OwnerSlot0`, `OwnerSlot1`,
 * `DiceCerts`), lockdown cannot actually revoke creator access to those 3
 * pages without also breaking owner access to the others. This is a known,
 * accepted gap pending hardware changes to add more RRAM info/data
 * memory-protection regions.
 */
typedef struct rram_ctrl_info_page {
  /**
   * Physical page index.
   *
   * For a real page (`emulated` = false), this is an info-partition page
   * index in [0, `RRAM_CTRL_PARAM_NUM_INFO_PAGES` - 1]. For an emulated page
   * (`emulated` = true), this is a data-partition page index at or after
   * `kRramCtrlEmulPageBase`.
   */
  uint32_t page_id;
  /**
   * Whether this page is emulated on the data partition rather than backed by
   * a real RRAM info page.
   */
  bool emulated;
} rram_ctrl_info_page_t;

/**
 * First data-partition page reserved for emulated info pages, and the number
 * of data pages reserved. All emulated pages share a single
 * memory-protection region covering this range.
 */
enum {
  kRramCtrlEmulPageBase = 4064,
  kRramCtrlEmulPageCount = 14,
  /**
   * Memory-protection region index (of `RRAM_CTRL_PARAM_NUM_REGIONS`) used
   * for the shared emulated-page region.
   */
  kRramCtrlEmulRegion = 0,
};

/**
 * Table of RRAM information pages.
 *
 * Columns: Name, physical page index, whether emulated.
 * We use an X macro to facilitate writing enums, switch statements, and unit
 * tests using the constants here, mirroring `FLASH_CTRL_INFO_PAGES_DEFINE`.
 */
// clang-format off
#define RRAM_CTRL_INFO_PAGES_DEFINE(X) \
  /**
   * Real, individually-protected info pages.
   */ \
  X(kRramCtrlInfoPageFactoryId,           0, false) \
  X(kRramCtrlInfoPageAttestationKeySeeds, 1, false) \
  X(kRramCtrlInfoPageFactoryCerts,        2, false) \
  X(kRramCtrlInfoPageCreatorSecret,       5, false) \
  X(kRramCtrlInfoPageOwnerSecret,         6, false) \
  X(kRramCtrlInfoPageWaferAuthSecret,     7, false) \
  /**
   * Emulated info pages, relocated onto the data partition. All share
   * `kRramCtrlEmulRegion`'s memory protection; see the TODO on
   * `rram_ctrl_info_page_t`.
   */ \
  X(kRramCtrlInfoPageOwnerReserved0,      kRramCtrlEmulPageBase + 0,  true) \
  X(kRramCtrlInfoPageOwnerReserved1,      kRramCtrlEmulPageBase + 1,  true) \
  X(kRramCtrlInfoPageOwnerReserved2,      kRramCtrlEmulPageBase + 2,  true) \
  X(kRramCtrlInfoPageOwnerReserved3,      kRramCtrlEmulPageBase + 3,  true) \
  X(kRramCtrlInfoPageBootData0,           kRramCtrlEmulPageBase + 4,  true) \
  X(kRramCtrlInfoPageBootData1,           kRramCtrlEmulPageBase + 5,  true) \
  X(kRramCtrlInfoPageOwnerSlot0,          kRramCtrlEmulPageBase + 6,  true) \
  X(kRramCtrlInfoPageOwnerSlot1,          kRramCtrlEmulPageBase + 7,  true) \
  X(kRramCtrlInfoPageCreatorReserved0,    kRramCtrlEmulPageBase + 8,  true) \
  X(kRramCtrlInfoPageOwnerReserved4,      kRramCtrlEmulPageBase + 9,  true) \
  X(kRramCtrlInfoPageOwnerReserved5,      kRramCtrlEmulPageBase + 10, true) \
  X(kRramCtrlInfoPageOwnerReserved6,      kRramCtrlEmulPageBase + 11, true) \
  X(kRramCtrlInfoPageOwnerReserved7,      kRramCtrlEmulPageBase + 12, true) \
  X(kRramCtrlInfoPageDiceCerts,           kRramCtrlEmulPageBase + 13, true) \
// clang-format on

/**
 * Helper macro for declaring an extern `rram_ctrl_info_page_t`.
 * @param name_ Name of the enumeration constant.
 * @param page_id_ Physical page index of the info page.
 * @param emulated_ Whether the page is emulated on the data partition.
 */
#define INFO_PAGE_STRUCT_DECL_(name_, page_id_, emulated_) \
  extern const rram_ctrl_info_page_t name_;

/**
 * Info pages.
 */
RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_DECL_);

#undef INFO_PAGE_STRUCT_DECL_

/**
 * The following constants represent the expected number of sec_mmio
 * register writes performed by functions provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 */
enum {
  kRramCtrlSecMmioDataDefaultPermsSet = 1,
  kRramCtrlSecMmioDataDefaultCfgSet = 1,
  kRramCtrlSecMmioInfoPermsSet = 1,
  kRramCtrlSecMmioInfoCfgSet = 1,
  kRramCtrlSecMmioInfoCfgLock = 1,
  kRramCtrlSecMmioInfoPageLockdown = 2,
  kRramCtrlSecMmioExecSet = 1,
  kRramCtrlSecMmioDataRegionProtect = 1,
  kRramCtrlSecMmioDataRegionProtectLock = 1,
  kRramCtrlSecMmioInit = 1,
};

/**
 * Kicks off the initialization of the RRAM controller.
 *
 * This must complete before RRAM can be accessed. The init status can be
 * queried by calling `rram_ctrl_status_get()` and checking `init_done`.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioInit)` when sec_mmio is being
 * used to check expectations.
 */
void rram_ctrl_init(void);

/**
 * Permanently disable the RRAM controller.
 */
void rram_ctrl_disable(void);

/**
 * Status bits.
 */
typedef struct rram_ctrl_status {
  /**
   * RRAM read FIFO full, software must consume data.
   */
  bool rd_full;
  /**
   * RRAM read FIFO empty.
   */
  bool rd_empty;
  /**
   * RRAM write FIFO full.
   */
  bool wr_full;
  /**
   * RRAM write FIFO empty, software must provide data.
   */
  bool wr_empty;
  /**
   * RRAM controller undergoing init.
   */
  bool init_done;
} rram_ctrl_status_t;

/**
 * Query the status registers on the RRAM controller.
 *
 * @param[out] status The current status of the RRAM controller.
 */
void rram_ctrl_status_get(rram_ctrl_status_t *status);

/**
 * Error code bits.
 */
typedef struct rram_ctrl_error_code {
  /**
   * Software has supplied an undefined RRAM operation.
   */
  bool op_err;
  /**
   * RRAM access permission error. Read the ERR_ADDR register for the
   * faulting address.
   */
  bool mp_err;
  /**
   * RRAM read error, could be an integrity error.
   */
  bool rd_err;
  /**
   * RRAM write error.
   */
  bool wr_err;
} rram_ctrl_error_code_t;

/**
 * Query the error code register on the RRAM controller.
 *
 * @param[out] error_code The current error code of the RRAM controller.
 */
void rram_ctrl_error_code_get(rram_ctrl_error_code_t *error_code);

/**
 * Reads data from the data partition.
 *
 * @param addr Address to read from.
 * @param word_count Number of bus words to read.
 * @param[out] data Buffer to store the read data. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rram_ctrl_data_read(uint32_t addr, uint32_t word_count, void *data);

/**
 * Reads data from an information page.
 *
 * @param info_page Information page to read from.
 * @param offset Offset from the start of the page.
 * @param word_count Number of bus words to read.
 * @param[out] data Buffer to store the read data. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rram_ctrl_info_read(const rram_ctrl_info_page_t *info_page,
                                uint32_t offset, uint32_t word_count,
                                void *data);

/**
 * Reads data from an information page, returning all zeros if a read error
 * code is encountered.
 *
 * @param info_page Information page to read from.
 * @param offset Offset from the start of the page.
 * @param word_count Number of bus words to read.
 * @param[out] data Buffer to store the read data. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rram_ctrl_info_read_zeros_on_read_error(
    const rram_ctrl_info_page_t *info_page, uint32_t offset,
    uint32_t word_count, void *data);

/**
 * Writes data to the data partition.
 *
 * RRAM supports direct overwrite; unlike flash, no erase is required before
 * writing.
 *
 * @param addr Address to write to.
 * @param word_count Number of bus words to write. Must be a multiple of 4.
 * @param data Data to write. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rram_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                 const void *data);

/**
 * Writes data to an information page.
 *
 * @param info_page Information page to write to.
 * @param offset Offset from the start of the page.
 * @param word_count Number of bus words to write. Must be a multiple of 4.
 * @param data Data to write. Must be word aligned.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t rram_ctrl_info_write(const rram_ctrl_info_page_t *info_page,
                                 uint32_t offset, uint32_t word_count,
                                 const void *data);

/**
 * A struct for specifying access permissions.
 *
 * RRAM has no separate erase permission; unlike flash, write operations
 * overwrite in place.
 *
 * rram_ctrl config registers use 4-bits for boolean values. Use
 * `kMultiBitBool4True` to enable and `kMultiBitBool4False` to disable
 * permissions.
 */
typedef struct rram_ctrl_perms {
  uint32_t _pad0 : 4;
  /**
   * Read.
   */
  uint32_t read : 4;
  /**
   * Write.
   */
  uint32_t write : 4;
  uint32_t _pad1 : 20;
} rram_ctrl_perms_t;
OT_ASSERT_SIZE(rram_ctrl_perms_t, 4);

/**
 * Sets default access permissions for the data partition.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioDataDefaultPermsSet)` when
 * sec_mmio is being used to check expectations.
 *
 * @param perms New permissions.
 */
void rram_ctrl_data_default_perms_set(rram_ctrl_perms_t perms);

/**
 * Sets access permissions for a real (non-emulated) info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioInfoPermsSet)` when sec_mmio is
 * being used to check expectations.
 *
 * @param info_page A real information page (`emulated` = false).
 * @param perms New permissions.
 */
void rram_ctrl_info_perms_set(const rram_ctrl_info_page_t *info_page,
                              rram_ctrl_perms_t perms);

/**
 * A struct for RRAM configuration settings.
 *
 * RRAM has no high-endurance concept; unlike flash, no wear-leveling
 * configuration is needed.
 *
 * rram_ctrl config registers use 4-bits for boolean values. Use
 * `kMultiBitBool4True` to enable and `kMultiBitBool4False` to disable these
 * settings.
 */
typedef struct rram_ctrl_cfg {
  uint32_t _pad0 : 12;
  /**
   * Scrambling.
   */
  uint32_t scrambling : 4;
  /**
   * ECC.
   */
  uint32_t ecc : 4;
  uint32_t _pad1 : 12;
} rram_ctrl_cfg_t;
OT_ASSERT_SIZE(rram_ctrl_cfg_t, 4);

/**
 * Sets default configuration settings for the data partition.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioDataDefaultCfgSet)` when
 * sec_mmio is being used to check expectations.
 *
 * @param cfg New configuration settings.
 */
void rram_ctrl_data_default_cfg_set(rram_ctrl_cfg_t cfg);

/**
 * Reads the current default configuration settings for the data partition.
 *
 * @return Current configuration settings.
 */
rram_ctrl_cfg_t rram_ctrl_data_default_cfg_get(void);

/**
 * Reads the boot data info page configuration settings from OTP.
 *
 * Reuses the same `CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG` OTP word and bit
 * layout as flash; the high-endurance field is ignored for RRAM.
 *
 * @return Current OTP configuration settings.
 */
rram_ctrl_cfg_t rram_ctrl_boot_data_cfg_get(void);

/**
 * A type for rram_ctrl memory protection region indices.
 */
typedef uint32_t rram_ctrl_region_index_t;

/**
 * Configure memory protection for a region of data-partition pages.
 *
 * Based on the `region` parameter, this function overwrites the
 * `MP_REGION_${region}` and `MP_REGION_CFG_${region}` registers. Calling
 * this function invalidates previously-configured protections for `region`.
 *
 * @param region The index of the region to protect.
 * @param page_offset The index of the first page in the region.
 * @param num_pages The number of pages in the region.
 * @param perms The read/write permissions for this region.
 * @param cfg RRAM config values that are used to fill in some fields of the
 *            `MP_REGION_CFG_${region}` register.
 * @param lock Lock the configuration for this region.
 */
void rram_ctrl_data_region_protect(rram_ctrl_region_index_t region,
                                   uint32_t page_offset, uint32_t num_pages,
                                   rram_ctrl_perms_t perms, rram_ctrl_cfg_t cfg,
                                   hardened_bool_t lock);

/**
 * Sets configuration settings for a real (non-emulated) info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioInfoCfgSet)` when sec_mmio is
 * being used to check expectations.
 *
 * @param info_page A real information page (`emulated` = false).
 * @param cfg New configuration settings.
 */
void rram_ctrl_info_cfg_set(const rram_ctrl_info_page_t *info_page,
                            rram_ctrl_cfg_t cfg);

/**
 * Write-locks configuration settings for a real (non-emulated) info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioInfoCfgLock)` when sec_mmio is
 * being used to check expectations.
 *
 * @param info_page A real information page (`emulated` = false).
 */
void rram_ctrl_info_cfg_lock(const rram_ctrl_info_page_t *info_page);

/**
 * Disables all access to a real (non-emulated) info page and locks its
 * configuration until reset.
 *
 * Zeroes both the cfg register (clearing all permissions and configuration
 * bits) and the regwen register (preventing further writes to cfg).
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioInfoPageLockdown)` when sec_mmio
 * is being used to check expectations.
 *
 * @param info_page A real information page (`emulated` = false).
 */
void rram_ctrl_info_page_lockdown(const rram_ctrl_info_page_t *info_page);

/**
 * Enable execution from RRAM.
 *
 * Note: an ePMP region must also be configured in order to execute code in
 * RRAM.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kRramCtrlSecMmioExecSet)` when sec_mmio is being
 * used to check expectations.
 *
 * @param exec_val Value to write to the `rram_ctrl.EXEC` register.
 * `RRAM_CTRL_PARAM_EXEC_EN` will enable execution, all other values will
 * disable execution.
 */
void rram_ctrl_exec_set(uint32_t exec_val);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RRAM_CTRL_H_
