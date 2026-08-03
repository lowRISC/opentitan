// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RRAM_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RRAM_CTRL_H_

#include <assert.h>
#include <limits.h>
#include <stdbool.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/rram_ctrl_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif

/**
 * A logical RRAM info page.
 *
 * Unlike flash, RRAM has only `RRAM_CTRL_PARAM_NUM_INFO_PAGES` (8) physical
 * info pages, too few for the 20 logical pages named in `nvm_info_page_t`.
 * The remaining pages are emulated on the data partition of the RRAM.
 * The permissions are currently per emulated page region and not per page.
 * This needs to be adjusted: https://github.com/lowRISC/opentitan/issues/30914.
 */
typedef struct rram_ctrl_info_page {
  /**
   * Physical page index.
   *
   * For a real page (`emulated` = false), this is an info-partition page
   * index in [0, `RRAM_CTRL_PARAM_NUM_INFO_PAGES` - 1]. For an emulated page
   * (`emulated` = true), this is a data-partition page index.
   */
  uint32_t page_id;
  /**
   * Whether this page is emulated on the data partition rather than backed by
   * a real RRAM info page.
   */
  bool emulated;
  /**
   * Number of contiguous physical pages backing this logical page.
   *
   * Real info pages are always 1 (there's no way to combine physical info
   * pages). Emulated pages can span multiple contiguous data-partition pages
   * to fit content larger than 512 bytes; callers reading/writing more than
   * `num_pages * 512` bytes will silently spill into the next logical page's
   * storage, since nothing enforces this bound at the read/write call site.
   */
  uint32_t num_pages;
} rram_ctrl_info_page_t;

/**
 * Two data-partition page ranges, each reserved at the tail of one firmware
 * slot (matching the linker's `_nvm_slot_reserved_bytes`, which carves the
 * same 32KiB out of every slot): Each has its own memory-protection region,
 * granted in full by `nvm_ctrl_init()`. Bootstrap/rescue's generic erase
 * and program paths exclude both ranges in full.
 */
enum {
  /**
   * Number of pages the linker reserves at the tail of every slot
   * (`_nvm_slot_reserved_bytes` in top_earlgrey_memory.ld, 32KiB).
   */
  kRramCtrlReservedPageCount = 0x8000 / RRAM_CTRL_PARAM_BYTES_PER_PAGE,

  kRramCtrlEmulPageEndA = RRAM_CTRL_PARAM_NUM_DATA_PAGES / 2,
  kRramCtrlEmulPageBaseA = kRramCtrlEmulPageEndA - kRramCtrlReservedPageCount,
  kRramCtrlEmulRegionA = 8,

  kRramCtrlEmulPageEndB = RRAM_CTRL_PARAM_NUM_DATA_PAGES,
  kRramCtrlEmulPageBaseB = kRramCtrlEmulPageEndB - kRramCtrlReservedPageCount,
  kRramCtrlEmulRegionB = 9,

  /**
   * Pages at the very tail of Region B's window reserved for OTP: read/write
   * protected in hardware.
   */
  kRramCtrlOtpPageCount = RRAM_CTRL_PARAM_NUM_OTP_PAGES,
};

/**
 * Table of RRAM information pages.
 *
 * Columns: Name, physical page index, whether emulated, number of contiguous
 * physical pages backing it (see `rram_ctrl_info_page_t.num_pages`).
 * We use an X macro to facilitate writing enums, switch statements, and unit
 * tests using the constants here, mirroring `FLASH_CTRL_INFO_PAGES_DEFINE`.
 *
 * Emulated-page offsets below are manually cumulative (each is the previous
 * entry's offset + its `num_pages`) since a page occupying more than one
 * slot has no entries of its own for its 2nd-Nth pages.
 */
// clang-format off
#define RRAM_CTRL_INFO_PAGES_DEFINE(X) \
  /**
   * Real, individually-protected info pages. Always 1 page each -- there's
   * no way to combine physical info pages, so anything needing more than
   * 512 bytes must be an emulated page instead (see below).
   */ \
  X(kRramCtrlInfoPageFactoryId,           0, false, 1) \
  X(kRramCtrlInfoPageAttestationKeySeeds, 1, false, 1) \
  X(kRramCtrlInfoPageCreatorSecret,       5, false, 1) \
  X(kRramCtrlInfoPageOwnerSecret,         6, false, 1) \
  X(kRramCtrlInfoPageWaferAuthSecret,     7, false, 1) \
  /**
   * Emulated info pages, relocated onto the data partition.
   *
   * All emulated pages are uniformly 4 pages (2048 bytes) each, even though
   * several don't strictly need it. Pages that DO need the full 2048
   * bytes:
   *  - `OwnerSlot0`/`OwnerSlot1`: back `owner_block_t`, which is 2048 bytes
   *    (`OT_ASSERT_SIZE(owner_block_t, 2048)`).
   *  - `DiceCerts`/`FactoryCerts`: share one `dice_page_t` buffer type and
   *    must be deliberately equal in size (see the `static_assert` in
   *    dice_chain.h), even though their actual content (~1.3KB and ~800
   *    bytes respectively) would technically fit in fewer.
   *  - `OwnerReserved0`: what ISFB owner configs point at
   *    (`isfb->bank=0,page=5`); needs the space for its strike region plus
   *    product expressions.
   *  - `OwnerReserved6`/`OwnerReserved7`: SKU extensions (e.g.
   *    `tpm_personalize_ext.c`'s TPM EK cert) write to them via the same
   *    `dice_page_t` buffer as `DiceCerts`/`FactoryCerts`, which is always a
   *    full `kDicePageDataSize`.
   */ \
  X(kRramCtrlInfoPageOwnerReserved0,   kRramCtrlEmulPageBaseB + 0,  true, 4) \
  X(kRramCtrlInfoPageOwnerReserved1,   kRramCtrlEmulPageBaseB + 4,  true, 4) \
  X(kRramCtrlInfoPageOwnerReserved2,   kRramCtrlEmulPageBaseB + 8,  true, 4) \
  X(kRramCtrlInfoPageOwnerReserved3,   kRramCtrlEmulPageBaseB + 12, true, 4) \
  X(kRramCtrlInfoPageOwnerReserved4,   kRramCtrlEmulPageBaseB + 16, true, 4) \
  X(kRramCtrlInfoPageOwnerReserved5,   kRramCtrlEmulPageBaseB + 20, true, 4) \
  X(kRramCtrlInfoPageOwnerReserved6,   kRramCtrlEmulPageBaseB + 24, true, 4) \
  X(kRramCtrlInfoPageOwnerReserved7,   kRramCtrlEmulPageBaseB + 28, true, 4) \
  X(kRramCtrlInfoPageBootData0,        kRramCtrlEmulPageBaseB + 32, true, 4) \
  X(kRramCtrlInfoPageBootData1,        kRramCtrlEmulPageBaseB + 36, true, 4) \
  X(kRramCtrlInfoPageOwnerSlot0,       kRramCtrlEmulPageBaseB + 40, true, 4) \
  X(kRramCtrlInfoPageOwnerSlot1,       kRramCtrlEmulPageBaseB + 44, true, 4) \
  X(kRramCtrlInfoPageDiceCerts,        kRramCtrlEmulPageBaseB + 48, true, 4) \
  X(kRramCtrlInfoPageFactoryCerts,     kRramCtrlEmulPageBaseB + 52, true, 4) \
  /**
   * In its own dedicated region (`kRramCtrlEmulRegionA`), not
   * `kRramCtrlEmulRegionB` above; see the comment there.
   */ \
  X(kRramCtrlInfoPageCreatorReserved0, kRramCtrlEmulPageBaseA + 0, true, 4) \
// clang-format on

/**
 * Total pages `RRAM_CTRL_INFO_PAGES_DEFINE` assigns within each region's
 * window, computed by walking the table rather than hand-counted, so a
 * future entry that doesn't fit is caught automatically instead of silently
 * landing past the window (into the next region, or -- for Region B --
 * into the hardware-protected OTP tail).
 */
#define INFO_PAGE_SUM_REGION_A_(name_, page_id_, emulated_, num_pages_) \
  +((emulated_) && (page_id_) >= kRramCtrlEmulPageBaseA &&              \
            (page_id_) < kRramCtrlEmulPageEndA                          \
        ? (num_pages_)                                                  \
        : 0)
#define INFO_PAGE_SUM_REGION_B_(name_, page_id_, emulated_, num_pages_) \
  +((emulated_) && (page_id_) >= kRramCtrlEmulPageBaseB &&              \
            (page_id_) < kRramCtrlEmulPageEndB                          \
        ? (num_pages_)                                                  \
        : 0)
enum {
  kRramCtrlInfoPagesRegionATotal =
      0 RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_SUM_REGION_A_),
  kRramCtrlInfoPagesRegionBTotal =
      0 RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_SUM_REGION_B_),
};
#undef INFO_PAGE_SUM_REGION_A_
#undef INFO_PAGE_SUM_REGION_B_
static_assert(kRramCtrlInfoPagesRegionATotal <= kRramCtrlReservedPageCount,
              "RRAM_CTRL_INFO_PAGES_DEFINE's Region A entries overflow "
              "kRramCtrlEmulRegionA's window");
static_assert(kRramCtrlInfoPagesRegionBTotal <=
                  kRramCtrlReservedPageCount - kRramCtrlOtpPageCount,
              "RRAM_CTRL_INFO_PAGES_DEFINE's Region B entries would overlap "
              "the OTP tail");

/**
 * Helper macro for declaring an extern `rram_ctrl_info_page_t`.
 * @param name_ Name of the enumeration constant.
 * @param page_id_ Physical page index of the info page.
 * @param emulated_ Whether the page is emulated on the data partition.
 * @param num_pages_ Number of contiguous physical pages backing this page.
 */
#define INFO_PAGE_STRUCT_DECL_(name_, page_id_, emulated_, num_pages_) \
  extern const rram_ctrl_info_page_t name_;

/**
 * Info pages.
 */
RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_STRUCT_DECL_);

#undef INFO_PAGE_STRUCT_DECL_

/**
 * Helper macro for declaring a `<name_>Size` compile-time constant: the
 * total on-NVM byte size backing a logical page, i.e.
 * `num_pages_ * RRAM_CTRL_PARAM_BYTES_PER_PAGE`. Callers should use these
 * instead of re-deriving a page's size from `num_pages` themselves, so the
 * page table in `RRAM_CTRL_INFO_PAGES_DEFINE` stays the only place page
 * counts are written down.
 * @param name_ Name of the enumeration constant.
 * @param page_id_ Physical page index of the info page.
 * @param emulated_ Whether the page is emulated on the data partition.
 * @param num_pages_ Number of contiguous physical pages backing this page.
 */
#define INFO_PAGE_SIZE_ENUM_(name_, page_id_, emulated_, num_pages_) \
  name_##Size = (num_pages_) * RRAM_CTRL_PARAM_BYTES_PER_PAGE,

enum { RRAM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_SIZE_ENUM_) };

#undef INFO_PAGE_SIZE_ENUM_

/**
 * Bitfields for `CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG` and
 * `CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG` OTP items.
 *
 * RRAM reuses the same OTP words and bit layout as flash_ctrl (the OTP
 * schema was not redesigned for RRAM); these are RRAM's own copies of
 * flash_ctrl.h's `FLASH_CTRL_OTP_FIELD_*` macros so that rram_ctrl does not
 * need to depend on the flash_ctrl driver just for these constants.
 *
 * Defined here to be able to use in tests.
 */
#define RRAM_CTRL_OTP_FIELD_SCRAMBLING \
  (bitfield_field32_t){.mask = UINT8_MAX, .index = CHAR_BIT * 0}
#define RRAM_CTRL_OTP_FIELD_ECC \
  (bitfield_field32_t){.mask = UINT8_MAX, .index = CHAR_BIT * 1}

/**
 * Bitfields for `CREATOR_SW_CFG_FLASH_HW_INFO_CFG_OVERRIDE` OTP item.
 *
 * See the note above: RRAM reuses flash_ctrl's OTP word/bit layout.
 *
 * Defined here to be able to use in tests.
 */
#define RRAM_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_SCRAMBLE_DIS \
  (bitfield_field32_t){.mask = UINT8_MAX, .index = CHAR_BIT * 0}
#define RRAM_CTRL_OTP_FIELD_HW_INFO_CFG_OVERRIDE_ECC_DIS \
  (bitfield_field32_t){.mask = UINT8_MAX, .index = CHAR_BIT * 1}

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
  // 2 writes: MP_REGION_${region} and MP_REGION_CFG_${region}.
  kRramCtrlSecMmioDataRegionProtect = 2,
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
 * @param num_pages The number of pages in the region, i.e. the region covers
 *                  the exclusive range `[page_offset, page_offset +
 *                  num_pages)`. Internally compensates for the hardware's
 *                  match logic, which is inclusive of `page_offset +
 *                  num_pages`. Must be nonzero: the hardware has no way to
 *                  express an empty region, so callers deriving this from
 *                  untrusted data must reject 0 themselves.
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
