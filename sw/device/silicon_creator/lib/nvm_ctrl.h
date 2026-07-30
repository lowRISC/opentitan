// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NVM_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NVM_CTRL_H_

#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/error.h"

// Hardware parameter and address constants.  Only nvm_ctrl.{h,c} may include
// these headers directly; all other callers use the NVM_* aliases below.
#include "hw/top/flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#ifdef HAS_RRAM_CTRL
#include "sw/device/silicon_creator/lib/drivers/rram_ctrl.h"

#include "hw/top/rram_ctrl_regs.h"
#endif  // HAS_RRAM_CTRL

#ifdef __cplusplus
extern "C" {
#endif

// ---------------------------------------------------------------------------
// NVM layout constants
// ---------------------------------------------------------------------------

#ifdef HAS_RRAM_CTRL
/** Byte size of one NVM page. */
#define NVM_BYTES_PER_PAGE RRAM_CTRL_PARAM_BYTES_PER_PAGE
/**
 * Byte size of one NVM program/read word.
 *
 * This is a fixed, tech-agnostic value (matching flash's
 * `FLASH_CTRL_PARAM_BYTES_PER_WORD`), not `RRAM_CTRL_PARAM_BYTES_PER_WORD`
 * (16): callers like `boot_data.c` use it to size wire-format struct fields
 * (e.g. `boot_data_t.is_valid`) that must stay identical regardless of NVM
 * technology. RRAM's actual write granularity (4x this, 16 bytes) is a
 * separate, driver-internal detail handled by `nvm_ctrl.c`/`rram_ctrl.c`.
 */
#define NVM_BYTES_PER_WORD 8
/**
 * Number of NVM banks.
 *
 * RRAM has no bank-erase concept, so the whole data partition is treated as
 * a single bank; `NVM_BYTES_PER_BANK`/`NVM_PAGES_PER_BANK` describe the full
 * data partition. Slot A/B addressing (the only thing that matters for
 * dual-bank redundancy) is computed from `NVM_DATA_BASE_ADDR`/
 * `NVM_DATA_SIZE_BYTES` directly and does not depend on this value.
 */
#define NVM_NUM_BANKS 1u
/** Number of data pages per NVM bank. */
#define NVM_PAGES_PER_BANK RRAM_CTRL_PARAM_NUM_DATA_PAGES
/** Byte size of one NVM bank. */
#define NVM_BYTES_PER_BANK (NVM_PAGES_PER_BANK * NVM_BYTES_PER_PAGE)
/**
 * Base address of the NVM data partition in the system memory map.
 *
 * This is the CPU-visible, memory-mapped execute-in-place window (used e.g.
 * to determine the current boot slot from the program counter), distinct
 * from the 0-based byte offsets `rram_ctrl_data_read`/`_write` operate on.
 */
#define NVM_DATA_BASE_ADDR TOP_EARLGREY_RRAM_CTRL_HOST_BASE_ADDR
/** Total byte size of the NVM data partition. */
#define NVM_DATA_SIZE_BYTES \
  (RRAM_CTRL_PARAM_NUM_DATA_PAGES * RRAM_CTRL_PARAM_BYTES_PER_PAGE)
#else
/** Byte size of one NVM page. */
#define NVM_BYTES_PER_PAGE FLASH_CTRL_PARAM_BYTES_PER_PAGE
/** Byte size of one NVM program/read word. */
#define NVM_BYTES_PER_WORD FLASH_CTRL_PARAM_BYTES_PER_WORD
/** Byte size of one NVM bank. */
#define NVM_BYTES_PER_BANK FLASH_CTRL_PARAM_BYTES_PER_BANK
/** Number of NVM banks. */
#define NVM_NUM_BANKS FLASH_CTRL_PARAM_REG_NUM_BANKS
/** Number of data pages per NVM bank. */
#define NVM_PAGES_PER_BANK FLASH_CTRL_PARAM_REG_PAGES_PER_BANK
/** Base address of the NVM data partition in the system memory map. */
#define NVM_DATA_BASE_ADDR TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR
/** Total byte size of the NVM data partition. */
#define NVM_DATA_SIZE_BYTES TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES
#endif  // HAS_RRAM_CTRL

/**
 * Exclusive upper bound, in bytes, of the NVM data partition actually usable
 * for generic firmware reads/writes/erases (bootstrap PAGE_PROGRAM/erase,
 * rescue firmware updates, ...).
 *
 * For RRAM, this stops before `kRramCtrlEmulPageBase`: everything from there
 * onward is either the emulated info-page region (OwnerSlot0/1, DiceCerts,
 * BootData0/1, ... -- only accessible through `nvm_ctrl_info_*()`, not plain
 * data reads/writes) or, past `kRramCtrlEmulPageBase +
 * kRramCtrlEmulPageCount`, a small tail reserved for OTP that's read/write
 * protected in hardware and must never be touched by software at all. For
 * flash, there is no such reserved tail, so this is just the full data
 * partition size.
 */
#ifdef HAS_RRAM_CTRL
#define NVM_USABLE_DATA_SIZE_BYTES (kRramCtrlEmulPageBase * NVM_BYTES_PER_PAGE)
#else
#define NVM_USABLE_DATA_SIZE_BYTES NVM_DATA_SIZE_BYTES
#endif  // HAS_RRAM_CTRL

/**
 * Page/byte count of one firmware slot (A or B).
 *
 * There are always exactly two slots, splitting the NVM data partition in
 * half regardless of technology: two banks of one slot each for flash, or one
 * bank of two slots for RRAM.
 */
#define NVM_PAGES_PER_SLOT ((NVM_NUM_BANKS * NVM_PAGES_PER_BANK) / 2)
#define NVM_BYTES_PER_SLOT (NVM_PAGES_PER_SLOT * NVM_BYTES_PER_PAGE)

/**
 * Byte size of one NVM program transaction / SPI `PAGE_PROGRAM` "page".
 *
 * This is the SPI `PAGE_PROGRAM` wrap-around unit `nvm_ctrl_page_program()`
 * uses internally, and the natural write-transaction size for the
 * underlying NVM technology. It is NOT the same concept as
 * `NVM_BYTES_PER_PAGE` (the erase granularity) -- the two happen to coincide
 * for RRAM (both 512), but differ for flash (2048 erase vs. 256
 * program/SPI-wrap).
 *
 * For RRAM, this matches `rram_phy_wr`'s store-buffer size (`BytesPerPage`
 * in `rram_ctrl.hjson`): a write up to this size commits to the array as a
 * single physical operation, and a write that straddles two of these units
 * costs an extra one. For flash, it's simply the SPI NOR industry-standard
 * `PAGE_PROGRAM` wrap size, with no known equivalent benefit to writing
 * more than one at a time.
 */
#ifdef HAS_RRAM_CTRL
#define NVM_PROG_PAGE_SIZE 512
#else
#define NVM_PROG_PAGE_SIZE 256
#endif

/** Value of a word in NVM after erase. */
enum { kNvmErasedWord = UINT32_MAX };

// ---------------------------------------------------------------------------
// Access permission and configuration types
// ---------------------------------------------------------------------------

/**
 * Access permission settings for an NVM page.
 *
 * Fields use `multi_bit_bool_t` values: `kMultiBitBool4True` enables the
 * operation; `kMultiBitBool4False` disables it. Raw hardware register values
 * are passed through without normalisation.
 */
typedef struct nvm_page_perms {
  multi_bit_bool_t read;
  multi_bit_bool_t write;
  multi_bit_bool_t erase;
} nvm_page_perms_t;

/**
 * Configuration settings for an NVM page.
 *
 * Fields use `multi_bit_bool_t` values: `kMultiBitBool4True` enables the
 * feature; `kMultiBitBool4False` disables it. Raw hardware register values
 * are passed through without normalisation.
 */
typedef struct nvm_page_cfg {
  multi_bit_bool_t scrambling;
  multi_bit_bool_t ecc;
  multi_bit_bool_t he;
} nvm_page_cfg_t;

/** Read, write, and erase all enabled. */
extern const nvm_page_perms_t kNvmPagePermsReadWrite;
/** Read enabled; write and erase disabled. */
extern const nvm_page_perms_t kNvmPagePermsReadOnly;
/** All permissions disabled. */
extern const nvm_page_perms_t kNvmPagePermsNone;
/** Erase enabled; read and write disabled. */
extern const nvm_page_perms_t kNvmPagePermsErase;

/** Scrambling and ECC enabled; high-endurance disabled. */
extern const nvm_page_cfg_t kNvmPageCfgScrambled;
/** Scrambling disabled; ECC enabled; high-endurance disabled. */
extern const nvm_page_cfg_t kNvmPageCfgPlain;
/** Scrambling, ECC, and high-endurance all disabled. */
extern const nvm_page_cfg_t kNvmPageCfgRaw;

// ---------------------------------------------------------------------------
// Info page identifiers
// ---------------------------------------------------------------------------

/**
 * Named NVM info partition pages.
 *
 * Enum values are contiguous: bank 0 pages 0-9 map to values 0-9, bank 1
 * pages 0-9 map to values 10-19.  The mapping to physical hardware addresses
 * is an internal detail of nvm_ctrl.c.
 */
typedef enum nvm_info_page {
  // Bank 0
  kNvmInfoPageFactoryId = 0,
  kNvmInfoPageCreatorSecret = 1,
  kNvmInfoPageOwnerSecret = 2,
  kNvmInfoPageWaferAuthSecret = 3,
  kNvmInfoPageAttestationKeySeeds = 4,
  kNvmInfoPageOwnerReserved0 = 5,
  kNvmInfoPageOwnerReserved1 = 6,
  kNvmInfoPageOwnerReserved2 = 7,
  kNvmInfoPageOwnerReserved3 = 8,
  kNvmInfoPageFactoryCerts = 9,
  // Bank 1
  kNvmInfoPageBootData0 = 10,
  kNvmInfoPageBootData1 = 11,
  kNvmInfoPageOwnerSlot0 = 12,
  kNvmInfoPageOwnerSlot1 = 13,
  kNvmInfoPageCreatorReserved0 = 14,
  kNvmInfoPageOwnerReserved4 = 15,
  kNvmInfoPageOwnerReserved5 = 16,
  kNvmInfoPageOwnerReserved6 = 17,
  kNvmInfoPageOwnerReserved7 = 18,
  kNvmInfoPageDiceCerts = 19,
} nvm_info_page_t;

/**
 * Byte size of `DiceCerts`/`FactoryCerts`, the two logical pages whose
 * on-NVM capacity varies with NVM technology (see `rram_ctrl.h`'s
 * `RRAM_CTRL_INFO_PAGES_DEFINE`, which is the source of truth these mirror
 * for RRAM). Every other logical page is exactly one `NVM_BYTES_PER_PAGE`,
 * on both technologies.
 */
#ifdef HAS_RRAM_CTRL
enum {
  kNvmInfoPageDiceCertsSize = kRramCtrlInfoPageDiceCertsSize,
  kNvmInfoPageFactoryCertsSize = kRramCtrlInfoPageFactoryCertsSize,
};

/**
 * Returns the physical RRAM info page descriptor for a logical page.
 *
 * The single source of truth for the logical-to-physical info page mapping
 * (built from `RRAM_CTRL_INFO_PAGES_DEFINE` in rram_ctrl.h), exported so
 * that `nvm_testutils.c` -- which talks to rram_ctrl via DIFs rather than
 * this driver, for host-injected provisioning/test code -- can share it
 * instead of maintaining a second, independently hand-written table that
 * can silently drift out of sync (as happened with `FactoryCerts`,
 * `OwnerSlot0`/`OwnerSlot1`, and `DiceCerts` growing to span multiple
 * physical pages here without the other table being updated to match).
 */
const rram_ctrl_info_page_t *nvm_ctrl_rram_page_info(nvm_info_page_t page);
#else
enum {
  kNvmInfoPageDiceCertsSize = NVM_BYTES_PER_PAGE,
  kNvmInfoPageFactoryCertsSize = NVM_BYTES_PER_PAGE,
};
#endif  // HAS_RRAM_CTRL

// ---------------------------------------------------------------------------
// SEC_MMIO write-increment constants
// ---------------------------------------------------------------------------
// Drop-in replacements for kFlashCtrlSecMmio* — identical numeric values.
// Callers keep their SEC_MMIO_WRITE_INCREMENT() call sites; only the constant
// name changes during migration.
//
// RRAM caveat: `kNvmCtrlSecMmioInfoPermsSet`, `kNvmCtrlSecMmioInfoCfgSet`,
// `kNvmCtrlSecMmioInfoCfgLock`, `kNvmCtrlSecMmioCertInfoPageCreatorCfg`, and
// `kNvmCtrlSecMmioCertInfoPageOwnerRestrict` are single constants shared by
// call sites that each target a caller-chosen `nvm_info_page_t`. For RRAM,
// `nvm_ctrl_info_perms_set`/`_cfg_set`/`_cfg_lock` are no-ops on an emulated
// info page (see the TODO on `rram_ctrl_info_page_t`), so any call site
// targeting an emulated page (e.g. OwnerSlot0/1, DiceCerts, OwnerReserved4-7)
// performs fewer actual register writes than these constants assume. This is
// a known, accepted gap for call sites whose target page varies at runtime:
// making those fully correct would require auditing every call site
// (ownership.c, owner_block.c, cert/dice_chain.c, manuf/ft_personalize.c,
// rom_ext.c, ...) to conditionally increment based on the specific page
// targeted. Call sites with a FIXED, statically-known page set don't have
// this excuse and must account for emulated pages precisely:
// `kNvmCtrlSecMmioCreatorInfoPagesLockdown` (fixed inside nvm_ctrl.c) does so
// below, and `boot_data.c`'s three call sites (always BootData0/BootData1,
// always emulated on RRAM) do so with their own `#ifdef HAS_RRAM_CTRL` at
// each `SEC_MMIO_WRITE_INCREMENT` rather than via this shared constant.
enum {
  kNvmCtrlSecMmioCertInfoPageCreatorCfg = 2,
  kNvmCtrlSecMmioCertInfoPageOwnerRestrict = 2,
  kNvmCtrlSecMmioCertInfoPagesOwnerRestrict = 5,
#ifdef HAS_RRAM_CTRL
  // 2 writes for each of the 4 pages (of the 7 in kNvmPagesNoOwnerAccess)
  // that are real (non-emulated) RRAM info pages: FactoryId, CreatorSecret,
  // OwnerSecret, WaferAuthSecret. The other 3 (BootData0, BootData1,
  // CreatorReserved0) are emulated and are skipped (see the TODO on
  // `rram_ctrl_info_page_t`).
  kNvmCtrlSecMmioCreatorInfoPagesLockdown = 8,
#else
  kNvmCtrlSecMmioCreatorInfoPagesLockdown = 14,
#endif
  kNvmCtrlSecMmioDataDefaultCfgSet = 1,
  kNvmCtrlSecMmioDataDefaultPermsSet = 1,
  kNvmCtrlSecMmioExecSet = 1,
  kNvmCtrlSecMmioInfoCfgSet = 1,
  kNvmCtrlSecMmioInfoCfgLock = 1,
  kNvmCtrlSecMmioInfoPageLockdown = 2,
  kNvmCtrlSecMmioInfoPermsSet = 1,
  kNvmCtrlSecMmioBankErasePermsSet = 1,
#ifdef HAS_RRAM_CTRL
  // 1 write from `rram_ctrl_data_default_cfg_set` (via `rram_ctrl_init`) plus
  // 1 from the `rram_ctrl_data_default_perms_set` call in `nvm_ctrl_init`.
  kNvmCtrlSecMmioInit = 2,
#else
  kNvmCtrlSecMmioInit = 3,
#endif
  kNvmCtrlSecMmioDataRegionProtect = 1,
  kNvmCtrlSecMmioDataRegionProtectLock = 1,
};

// ---------------------------------------------------------------------------
// Lifecycle
// ---------------------------------------------------------------------------

/**
 * Kicks off initialization of the NVM controller.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioInit)` when sec_mmio is used.
 */
void nvm_ctrl_init(void);

/**
 * Permanently disables the NVM controller.
 */
void nvm_ctrl_disable(void);

// ---------------------------------------------------------------------------
// Wire-format bridge (ownership layer only)
// ---------------------------------------------------------------------------

/**
 * Translate a wire-format (bank, page) pair to a typed info page enum value.
 *
 * Intended for use only at the ownership-layer boundary, where page addresses
 * are read from on-flash owner configuration structs that store raw bank and
 * page integers.  All NVM I/O then proceeds through the enum-based API.
 *
 * @param bank Bank index (must be < 2; this is a fixed wire-format constant,
 *             independent of the number of banks the underlying NVM
 *             technology actually has).
 * @param page Page index within the info partition type 0 (must be < 10).
 * @param[out] out Translated info page enum value.
 * @return kErrorOk on success, kErrorNvmCtrlInvalidInfoPage if out of range.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_page_lookup(uint8_t bank, uint8_t page,
                                      nvm_info_page_t *out);

// ---------------------------------------------------------------------------
// Data partition I/O
// ---------------------------------------------------------------------------

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_read(uint32_t addr, uint32_t word_count, void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                const void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_erase(uint32_t addr);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr);

/**
 * Erases all NVM data banks.
 *
 * Enables bank-erase permissions, erases every bank, then re-disables
 * bank-erase permissions.  Bank count and addresses are internal details.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_chip_erase(void);

/**
 * Verifies that all NVM data banks have been erased.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_chip_erase_verify(void);

/**
 * Programs up to 256 bytes of NVM data starting at `addr`.
 *
 * If `byte_count` is not a multiple of the NVM word size it is rounded up to
 * the next word boundary and padding bytes in `data` are set to 0xff.  If
 * `addr` is not 256-byte aligned the write is split so the first chunk fills
 * up to the 256-byte boundary and the second starts at the aligned address,
 * matching SPI PAGE_PROGRAM wrapping semantics.  Write permissions are managed
 * internally; the caller is responsible for address range validation.
 *
 * @param addr  Start address; must be NVM-word aligned.
 * @param byte_count  Number of bytes to write.
 * @param data  Buffer; must be word aligned with room for up to one extra word
 *              of 0xff padding beyond `byte_count`.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_page_program(uint32_t addr, size_t byte_count,
                                  uint8_t *data);

/**
 * Erases the 4 KiB sector containing `addr` in the data partition.
 *
 * Because the NVM page size is 2 KiB, erasing a 4 KiB sector requires two
 * consecutive page erases.  `addr` is truncated to the nearest 4 KiB boundary
 * before erasing; the caller is responsible for range validation.
 * Erase permissions are managed internally.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_sector_erase(uint32_t addr);

// ---------------------------------------------------------------------------
// Info page I/O
// ---------------------------------------------------------------------------

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_read(nvm_info_page_t page, uint32_t offset,
                               uint32_t word_count, void *data);

/**
 * Read from an info page, returning all-zeros words on a read error.
 */
OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_read_zeros_on_read_error(nvm_info_page_t page,
                                                   uint32_t offset,
                                                   uint32_t word_count,
                                                   void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_write(nvm_info_page_t page, uint32_t offset,
                                uint32_t word_count, const void *data);

OT_WARN_UNUSED_RESULT
rom_error_t nvm_ctrl_info_erase(nvm_info_page_t page);

// ---------------------------------------------------------------------------
// Permissions and configuration
// ---------------------------------------------------------------------------

/**
 * Sets default access permissions for the data partition.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioDataDefaultPermsSet)`.
 */
void nvm_ctrl_data_default_perms_set(nvm_page_perms_t perms);

/**
 * Sets access permissions for a named info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioInfoPermsSet)`.
 */
void nvm_ctrl_info_perms_set(nvm_info_page_t page, nvm_page_perms_t perms);

/**
 * Sets default configuration for the data partition.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioDataDefaultCfgSet)`.
 */
void nvm_ctrl_data_default_cfg_set(nvm_page_cfg_t cfg);

/** Returns the current default configuration for the data partition. */
nvm_page_cfg_t nvm_ctrl_data_default_cfg_get(void);

/** Returns the boot-data info page configuration read from OTP. */
nvm_page_cfg_t nvm_ctrl_boot_data_cfg_get(void);

/**
 * Sets configuration for a named info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioInfoCfgSet)`.
 */
void nvm_ctrl_info_cfg_set(nvm_info_page_t page, nvm_page_cfg_t cfg);

/**
 * Write-locks configuration for a named info page.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioInfoCfgLock)`.
 */
void nvm_ctrl_info_cfg_lock(nvm_info_page_t page);

// ---------------------------------------------------------------------------
// Data region protection
// ---------------------------------------------------------------------------

/**
 * Configure memory protection for a data partition region.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioDataRegionProtect)` (plus
 * `kNvmCtrlSecMmioDataRegionProtectLock` when `lock` is true).
 */
void nvm_ctrl_data_region_protect(uint32_t region, uint32_t page_offset,
                                  uint32_t num_pages, nvm_page_perms_t perms,
                                  nvm_page_cfg_t cfg, hardened_bool_t lock);

/**
 * Set bank erase permissions for both NVM banks.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioBankErasePermsSet)`.
 */
void nvm_ctrl_bank_erase_perms_set(hardened_bool_t enable);

/**
 * Enable or disable execution from NVM.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioExecSet)`.
 *
 * @param exec_val `FLASH_CTRL_PARAM_EXEC_EN` enables execution; all other
 *                 values disable it.
 */
void nvm_ctrl_exec_set(uint32_t exec_val);

// ---------------------------------------------------------------------------
// Lockdown and certificate page management
// ---------------------------------------------------------------------------

/** Certificate page configuration: scrambling and ECC enabled. */
extern const nvm_page_cfg_t kNvmCertInfoPageCfg;
/** Creator access: read, write, and erase enabled. */
extern const nvm_page_perms_t kNvmCertInfoPageCreatorAccess;
/** Owner access: read enabled; write and erase disabled. */
extern const nvm_page_perms_t kNvmCertInfoPageOwnerAccess;

/**
 * Disables all access to silicon creator info pages until next reset.
 *
 * Must be called in ROM_EXT before handing over execution to the first owner
 * boot stage.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioCreatorInfoPagesLockdown)`.
 */
void nvm_ctrl_creator_info_pages_lockdown(void);

/**
 * Configures a certificate info page for full creator access.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioCertInfoPageCreatorCfg)`.
 */
void nvm_ctrl_cert_info_page_creator_cfg(nvm_info_page_t page);

/**
 * Restricts a certificate info page to read-only for the silicon owner.
 *
 * The caller is responsible for calling
 * `SEC_MMIO_WRITE_INCREMENT(kNvmCtrlSecMmioCertInfoPageOwnerRestrict)`.
 */
void nvm_ctrl_cert_info_page_owner_restrict(nvm_info_page_t page);

// clang-format off
/**
 * Bitfields for the `access` word of owner NVM region configs.
 */
#define NVM_CONFIG_READ                 ((bitfield_field32_t) { .mask = 0xF, .index = 0 })
#define NVM_CONFIG_PROGRAM              ((bitfield_field32_t) { .mask = 0xF, .index = 4 })
#define NVM_CONFIG_ERASE                ((bitfield_field32_t) { .mask = 0xF, .index = 8 })
#define NVM_CONFIG_PROTECT_WHEN_PRIMARY ((bitfield_field32_t) { .mask = 0xF, .index = 24 })
#define NVM_CONFIG_LOCK                 ((bitfield_field32_t) { .mask = 0xF, .index = 28 })

/**
 * Bitfields for the `properties` word of owner NVM region configs.
 */
#define NVM_CONFIG_SCRAMBLE             ((bitfield_field32_t) { .mask = 0xF, .index = 0 })
#define NVM_CONFIG_ECC                  ((bitfield_field32_t) { .mask = 0xF, .index = 4 })
#define NVM_CONFIG_HIGH_ENDURANCE       ((bitfield_field32_t) { .mask = 0xF, .index = 8 })
// clang-format on

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_NVM_CTRL_H_
