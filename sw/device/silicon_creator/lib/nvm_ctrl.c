// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"

#ifdef HAS_RRAM_CTRL
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/drivers/rram_ctrl.h"
#else
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#endif  // HAS_RRAM_CTRL

// ---------------------------------------------------------------------------
// Internal: info page count per bank in the wire-format (bank, page) address
// bridge (see `nvm_ctrl_info_page_lookup`).
//
// These are fixed constants independent of NVM technology: on-flash owner
// config structs encode info pages as (bank, page) pairs assuming 2 banks of
// 10 pages each, matching flash's original type-0 info partition layout.
// `NVM_NUM_BANKS` must not be used here instead of `kNvmWireFormatBankCount`:
// it is a hardware-derived value (1 for RRAM, which has no bank concept) and
// would incorrectly reject bank-1 pages (BootData0/1, OwnerSlot0/1,
// DiceCerts, ...) that owner configs still legitimately encode.
// ---------------------------------------------------------------------------
enum {
  kNvmInfoPagesPerBank = 10,
  kNvmWireFormatBankCount = 2,
};

// ---------------------------------------------------------------------------
// Internal: mapping from nvm_info_page_t enum to a driver-level page pointer.
// Order must match nvm_info_page_t definition in nvm_ctrl.h.
// ---------------------------------------------------------------------------
#ifdef HAS_RRAM_CTRL
static const rram_ctrl_info_page_t *const kPageTable[] = {
    [kNvmInfoPageFactoryId] = &kRramCtrlInfoPageFactoryId,
    [kNvmInfoPageCreatorSecret] = &kRramCtrlInfoPageCreatorSecret,
    [kNvmInfoPageOwnerSecret] = &kRramCtrlInfoPageOwnerSecret,
    [kNvmInfoPageWaferAuthSecret] = &kRramCtrlInfoPageWaferAuthSecret,
    [kNvmInfoPageAttestationKeySeeds] = &kRramCtrlInfoPageAttestationKeySeeds,
    [kNvmInfoPageOwnerReserved0] = &kRramCtrlInfoPageOwnerReserved0,
    [kNvmInfoPageOwnerReserved1] = &kRramCtrlInfoPageOwnerReserved1,
    [kNvmInfoPageOwnerReserved2] = &kRramCtrlInfoPageOwnerReserved2,
    [kNvmInfoPageOwnerReserved3] = &kRramCtrlInfoPageOwnerReserved3,
    [kNvmInfoPageFactoryCerts] = &kRramCtrlInfoPageFactoryCerts,
    [kNvmInfoPageBootData0] = &kRramCtrlInfoPageBootData0,
    [kNvmInfoPageBootData1] = &kRramCtrlInfoPageBootData1,
    [kNvmInfoPageOwnerSlot0] = &kRramCtrlInfoPageOwnerSlot0,
    [kNvmInfoPageOwnerSlot1] = &kRramCtrlInfoPageOwnerSlot1,
    [kNvmInfoPageCreatorReserved0] = &kRramCtrlInfoPageCreatorReserved0,
    [kNvmInfoPageOwnerReserved4] = &kRramCtrlInfoPageOwnerReserved4,
    [kNvmInfoPageOwnerReserved5] = &kRramCtrlInfoPageOwnerReserved5,
    [kNvmInfoPageOwnerReserved6] = &kRramCtrlInfoPageOwnerReserved6,
    [kNvmInfoPageOwnerReserved7] = &kRramCtrlInfoPageOwnerReserved7,
    [kNvmInfoPageDiceCerts] = &kRramCtrlInfoPageDiceCerts,
};
#else
static const flash_ctrl_info_page_t *const kPageTable[] = {
    [kNvmInfoPageFactoryId] = &kFlashCtrlInfoPageFactoryId,
    [kNvmInfoPageCreatorSecret] = &kFlashCtrlInfoPageCreatorSecret,
    [kNvmInfoPageOwnerSecret] = &kFlashCtrlInfoPageOwnerSecret,
    [kNvmInfoPageWaferAuthSecret] = &kFlashCtrlInfoPageWaferAuthSecret,
    [kNvmInfoPageAttestationKeySeeds] = &kFlashCtrlInfoPageAttestationKeySeeds,
    [kNvmInfoPageOwnerReserved0] = &kFlashCtrlInfoPageOwnerReserved0,
    [kNvmInfoPageOwnerReserved1] = &kFlashCtrlInfoPageOwnerReserved1,
    [kNvmInfoPageOwnerReserved2] = &kFlashCtrlInfoPageOwnerReserved2,
    [kNvmInfoPageOwnerReserved3] = &kFlashCtrlInfoPageOwnerReserved3,
    [kNvmInfoPageFactoryCerts] = &kFlashCtrlInfoPageFactoryCerts,
    [kNvmInfoPageBootData0] = &kFlashCtrlInfoPageBootData0,
    [kNvmInfoPageBootData1] = &kFlashCtrlInfoPageBootData1,
    [kNvmInfoPageOwnerSlot0] = &kFlashCtrlInfoPageOwnerSlot0,
    [kNvmInfoPageOwnerSlot1] = &kFlashCtrlInfoPageOwnerSlot1,
    [kNvmInfoPageCreatorReserved0] = &kFlashCtrlInfoPageCreatorReserved0,
    [kNvmInfoPageOwnerReserved4] = &kFlashCtrlInfoPageOwnerReserved4,
    [kNvmInfoPageOwnerReserved5] = &kFlashCtrlInfoPageOwnerReserved5,
    [kNvmInfoPageOwnerReserved6] = &kFlashCtrlInfoPageOwnerReserved6,
    [kNvmInfoPageOwnerReserved7] = &kFlashCtrlInfoPageOwnerReserved7,
    [kNvmInfoPageDiceCerts] = &kFlashCtrlInfoPageDiceCerts,
};
#endif  // HAS_RRAM_CTRL

// The wire format reserves 2 banks x kNvmInfoPagesPerBank addressable slots,
// independent of the number of banks the underlying technology actually has.
static_assert(ARRAYSIZE(kPageTable) <= 2 * kNvmInfoPagesPerBank,
              "More named pages than the wire format supports");

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

#ifdef HAS_RRAM_CTRL
static const rram_ctrl_info_page_t *page_ptr(nvm_info_page_t page) {
  HARDENED_CHECK_LT((uint32_t)page, ARRAYSIZE(kPageTable));
  return kPageTable[(uint32_t)page];
}

const rram_ctrl_info_page_t *nvm_ctrl_rram_page_info(nvm_info_page_t page) {
  return page_ptr(page);
}

static rram_ctrl_perms_t perms_to_rram(nvm_page_perms_t p) {
  return (rram_ctrl_perms_t){
      .read = (uint32_t)p.read,
      .write = (uint32_t)p.write,
  };
}

static rram_ctrl_cfg_t cfg_to_rram(nvm_page_cfg_t c) {
  return (rram_ctrl_cfg_t){
      .scrambling = (uint32_t)c.scrambling,
      .ecc = (uint32_t)c.ecc,
  };
}

static nvm_page_cfg_t cfg_from_rram(rram_ctrl_cfg_t c) {
  return (nvm_page_cfg_t){
      .scrambling = (multi_bit_bool_t)c.scrambling,
      .ecc = (multi_bit_bool_t)c.ecc,
      .he = kMultiBitBool4False,
  };
}

/**
 * Overwrites an info page with the all-1s "erased" pattern.
 *
 * RRAM has no erase primitive; this approximates flash's per-page erase by
 * directly overwriting the page's contents, for both real and emulated pages
 * (emulated pages are addressed individually within the shared data-partition
 * region, so this only touches the target page's own bytes).
 */
OT_WARN_UNUSED_RESULT
static rom_error_t rram_info_page_erase(const rram_ctrl_info_page_t *p) {
  enum { kChunkWords = 64 };
  uint32_t chunk[kChunkWords];
  memset(chunk, 0xff, sizeof(chunk));

  uint32_t words_left = NVM_BYTES_PER_PAGE / sizeof(uint32_t);
  uint32_t word_offset = 0;
  while (words_left > 0) {
    uint32_t n = words_left < kChunkWords ? words_left : kChunkWords;
    rom_error_t err;
    if (p->emulated) {
      err = rram_ctrl_data_write(
          p->page_id * NVM_BYTES_PER_PAGE + word_offset * sizeof(uint32_t), n,
          chunk);
    } else {
      err = rram_ctrl_info_write(p, word_offset * sizeof(uint32_t), n, chunk);
    }
    HARDENED_RETURN_IF_ERROR(err);
    word_offset += n;
    words_left -= n;
  }
  return kErrorOk;
}
#else
static const flash_ctrl_info_page_t *page_ptr(nvm_info_page_t page) {
  HARDENED_CHECK_LT((uint32_t)page, ARRAYSIZE(kPageTable));
  return kPageTable[(uint32_t)page];
}

static flash_ctrl_perms_t perms_to_flash(nvm_page_perms_t p) {
  return (flash_ctrl_perms_t){
      .read = (uint32_t)p.read,
      .write = (uint32_t)p.write,
      .erase = (uint32_t)p.erase,
  };
}

static flash_ctrl_cfg_t cfg_to_flash(nvm_page_cfg_t c) {
  return (flash_ctrl_cfg_t){
      .scrambling = (uint32_t)c.scrambling,
      .ecc = (uint32_t)c.ecc,
      .he = (uint32_t)c.he,
  };
}

static nvm_page_cfg_t cfg_from_flash(flash_ctrl_cfg_t c) {
  return (nvm_page_cfg_t){
      .scrambling = (multi_bit_bool_t)c.scrambling,
      .ecc = (multi_bit_bool_t)c.ecc,
      .he = (multi_bit_bool_t)c.he,
  };
}
#endif  // HAS_RRAM_CTRL

// ---------------------------------------------------------------------------
// Named constants
// ---------------------------------------------------------------------------

const nvm_page_perms_t kNvmPagePermsReadWrite = {.read = kMultiBitBool4True,
                                                 .write = kMultiBitBool4True,
                                                 .erase = kMultiBitBool4True};
const nvm_page_perms_t kNvmPagePermsReadOnly = {.read = kMultiBitBool4True,
                                                .write = kMultiBitBool4False,
                                                .erase = kMultiBitBool4False};
const nvm_page_perms_t kNvmPagePermsNone = {.read = kMultiBitBool4False,
                                            .write = kMultiBitBool4False,
                                            .erase = kMultiBitBool4False};
const nvm_page_perms_t kNvmPagePermsErase = {.read = kMultiBitBool4False,
                                             .write = kMultiBitBool4False,
                                             .erase = kMultiBitBool4True};

const nvm_page_cfg_t kNvmPageCfgScrambled = {.scrambling = kMultiBitBool4True,
                                             .ecc = kMultiBitBool4True,
                                             .he = kMultiBitBool4False};
const nvm_page_cfg_t kNvmPageCfgPlain = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4True,
                                         .he = kMultiBitBool4False};
const nvm_page_cfg_t kNvmPageCfgRaw = {.scrambling = kMultiBitBool4False,
                                       .ecc = kMultiBitBool4False,
                                       .he = kMultiBitBool4False};

const nvm_page_cfg_t kNvmCertInfoPageCfg = {.scrambling = kMultiBitBool4True,
                                            .ecc = kMultiBitBool4True,
                                            .he = kMultiBitBool4False};
const nvm_page_perms_t kNvmCertInfoPageCreatorAccess = {
    .read = kMultiBitBool4True,
    .write = kMultiBitBool4True,
    .erase = kMultiBitBool4True};
const nvm_page_perms_t kNvmCertInfoPageOwnerAccess = {
    .read = kMultiBitBool4True,
    .write = kMultiBitBool4False,
    .erase = kMultiBitBool4False};

// ---------------------------------------------------------------------------
// Wire-format bridge
// ---------------------------------------------------------------------------

rom_error_t nvm_ctrl_info_page_lookup(uint8_t bank, uint8_t page,
                                      nvm_info_page_t *out) {
  if ((uint32_t)bank >= (uint32_t)kNvmWireFormatBankCount ||
      (uint32_t)page >= (uint32_t)kNvmInfoPagesPerBank) {
    return kErrorNvmCtrlInvalidInfoPage;
  }
  *out = (nvm_info_page_t)(bank * kNvmInfoPagesPerBank + page);
  return kErrorOk;
}

static const nvm_info_page_t kNvmPagesNoOwnerAccess[] = {
    kNvmInfoPageFactoryId,        kNvmInfoPageCreatorSecret,
    kNvmInfoPageOwnerSecret,      kNvmInfoPageWaferAuthSecret,
    kNvmInfoPageBootData0,        kNvmInfoPageBootData1,
    kNvmInfoPageCreatorReserved0,
};

enum {
  kNvmPagesNoOwnerAccessCount = ARRAYSIZE(kNvmPagesNoOwnerAccess),
};

// ---------------------------------------------------------------------------
// Technology-specific implementation.
//
// Every `nvm_ctrl_*` function declared in nvm_ctrl.h (besides the
// tech-independent ones above and the cert-page helpers below, which are
// built on top of these) is implemented once here for RRAM and once for
// flash, rather than function-by-function, to keep each technology's full
// behavior readable as a single, self-contained unit.
// ---------------------------------------------------------------------------

#ifdef HAS_RRAM_CTRL

void nvm_ctrl_init(void) {
  rram_ctrl_init();
  // `DEFAULT_REGION.RD_EN` resets to false in hardware, and boot data lives
  // on an emulated info page (mapped onto the data partition), so it must be
  // persistently enabled here rather than only bracketing individual
  // operations like `nvm_ctrl_page_program` does.
  rram_ctrl_data_default_perms_set((rram_ctrl_perms_t){
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4False,
  });
  // Emulated info pages (e.g. OwnerSlot0/1, DiceCerts, BootData0/1) don't
  // get individual permissions like real info pages; they all share this one
  // memory-protection region instead. Grant it read/write access so they can
  // be written during boot.
  rram_ctrl_data_region_protect(
      kRramCtrlEmulRegion, kRramCtrlEmulPageBase, kRramCtrlEmulPageCount,
      (rram_ctrl_perms_t){
          .read = kMultiBitBool4True,
          .write = kMultiBitBool4True,
      },
      rram_ctrl_data_default_cfg_get(), kHardenedBoolFalse);
  // Unlocked, `rram_ctrl_data_region_protect()` performs 2 sec_mmio-tracked
  // writes (MP_REGION_${region} and MP_REGION_CFG_${region}), not the 1
  // implied by `kRramCtrlSecMmioDataRegionProtect` -- that constant appears
  // to under-count by one; using the literal here instead of relying on it.
  SEC_MMIO_WRITE_INCREMENT(2);
}

void nvm_ctrl_disable(void) { rram_ctrl_disable(); }

rom_error_t nvm_ctrl_data_read(uint32_t addr, uint32_t word_count, void *data) {
  return rram_ctrl_data_read(addr, word_count, data);
}

rom_error_t nvm_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                const void *data) {
  return rram_ctrl_data_write(addr, word_count, data);
}

rom_error_t nvm_ctrl_data_erase(uint32_t addr) {
  // RRAM supports direct overwrite; no erase step is required before a
  // write.
  (void)addr;
  return kErrorOk;
}

rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr) {
  (void)addr;
  return kErrorOk;
}

rom_error_t nvm_ctrl_chip_erase(void) { return kErrorOk; }

rom_error_t nvm_ctrl_chip_erase_verify(void) { return kErrorOk; }

rom_error_t nvm_ctrl_page_program(uint32_t addr, size_t byte_count,
                                  uint8_t *data) {
  enum {
    kProgPageSize = NVM_PROG_PAGE_SIZE,
    kProgPageMask = kProgPageSize - 1,
  };

  // Round up to next NVM word and fill missing bytes with 0xff.
  size_t word_misalignment = byte_count & (NVM_BYTES_PER_WORD - 1);
  if (word_misalignment > 0) {
    size_t pad = NVM_BYTES_PER_WORD - word_misalignment;
    for (size_t i = 0; i < pad; ++i) {
      data[byte_count++] = 0xff;
    }
  }
  size_t rem_word_count = byte_count / sizeof(uint32_t);

  // Unlike flash, RRAM's memory protection also gates the FIFO-transaction
  // read path used by `rram_ctrl_data_write()`'s internal read-modify-write
  // of unaligned partial granules, so read must be enabled here in addition
  // to write.
  rram_ctrl_data_default_perms_set((rram_ctrl_perms_t){
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
  });
  // Split the write if addr is not `kProgPageSize`-aligned: first chunk fills
  // up to the page boundary, second chunk starts at the aligned address (SPI
  // PAGE_PROGRAM wrapping semantics). `rram_ctrl_data_write` itself handles
  // any addr/word_count alignment, so no further splitting is needed within
  // each chunk.
  rom_error_t err_0 = kErrorOk;
  size_t prog_page_misalignment = addr & kProgPageMask;
  if (prog_page_misalignment > 0) {
    size_t word_count =
        (kProgPageSize - prog_page_misalignment) / sizeof(uint32_t);
    if (word_count > rem_word_count) {
      word_count = rem_word_count;
    }
    err_0 = rram_ctrl_data_write(addr, (uint32_t)word_count, data);
    rem_word_count -= word_count;
    data += word_count * sizeof(uint32_t);
    addr &= ~(uint32_t)kProgPageMask;
  }
  rom_error_t err_1 = kErrorOk;
  if (rem_word_count > 0) {
    err_1 = rram_ctrl_data_write(addr, (uint32_t)rem_word_count, data);
  }
  rram_ctrl_data_default_perms_set((rram_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
  });
  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

rom_error_t nvm_ctrl_sector_erase(uint32_t addr) {
  // RRAM supports direct overwrite; no erase step is required.
  (void)addr;
  return kErrorOk;
}

rom_error_t nvm_ctrl_info_read(nvm_info_page_t page, uint32_t offset,
                               uint32_t word_count, void *data) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    return rram_ctrl_data_read(p->page_id * NVM_BYTES_PER_PAGE + offset,
                               word_count, data);
  }
  return rram_ctrl_info_read(p, offset, word_count, data);
}

rom_error_t nvm_ctrl_info_read_zeros_on_read_error(nvm_info_page_t page,
                                                   uint32_t offset,
                                                   uint32_t word_count,
                                                   void *data) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    // Emulated pages are plain data-partition reads; there is no separate
    // "zeros on read error" data-partition primitive to fall back to.
    return rram_ctrl_data_read(p->page_id * NVM_BYTES_PER_PAGE + offset,
                               word_count, data);
  }
  return rram_ctrl_info_read_zeros_on_read_error(p, offset, word_count, data);
}

rom_error_t nvm_ctrl_info_write(nvm_info_page_t page, uint32_t offset,
                                uint32_t word_count, const void *data) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    return rram_ctrl_data_write(p->page_id * NVM_BYTES_PER_PAGE + offset,
                                word_count, data);
  }
  return rram_ctrl_info_write(p, offset, word_count, data);
}

rom_error_t nvm_ctrl_info_erase(nvm_info_page_t page) {
  return rram_info_page_erase(page_ptr(page));
}

void nvm_ctrl_data_default_perms_set(nvm_page_perms_t perms) {
  rram_ctrl_data_default_perms_set(perms_to_rram(perms));
}

// clang-format off
// NOTE (RRAM): the functions below are no-ops for emulated info pages, since
// emulated pages share one memory-protection region with a fixed,
// always-open policy and cannot be configured individually; see the TODO on
// `rram_ctrl_info_page_t`. Callers at existing SEC_MMIO_WRITE_INCREMENT()
// call sites assume a fixed number of actual register writes regardless of
// which page they target; on an emulated page these no-ops perform fewer
// (typically zero) writes than that, so `sec_mmio_check_counters()` will see
// fewer actual writes than expected on any boot path that calls one of these
// on an emulated page. Auditing/adjusting those call sites (in ownership.c,
// boot_data.c, owner_block.c, cert/dice_chain.c, manuf/ft_personalize.c,
// rom_ext.c, etc.) to account for real vs. emulated pages is a known,
// accepted follow-up, not solved here.
// clang-format on
void nvm_ctrl_info_perms_set(nvm_info_page_t page, nvm_page_perms_t perms) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    return;
  }
  rram_ctrl_info_perms_set(p, perms_to_rram(perms));
}

void nvm_ctrl_data_default_cfg_set(nvm_page_cfg_t cfg) {
  rram_ctrl_data_default_cfg_set(cfg_to_rram(cfg));
}

nvm_page_cfg_t nvm_ctrl_data_default_cfg_get(void) {
  return cfg_from_rram(rram_ctrl_data_default_cfg_get());
}

nvm_page_cfg_t nvm_ctrl_boot_data_cfg_get(void) {
  return cfg_from_rram(rram_ctrl_boot_data_cfg_get());
}

// See the RRAM emulated-page NOTE above `nvm_ctrl_info_perms_set`.
void nvm_ctrl_info_cfg_set(nvm_info_page_t page, nvm_page_cfg_t cfg) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    return;
  }
  rram_ctrl_info_cfg_set(p, cfg_to_rram(cfg));
}

// See the RRAM emulated-page NOTE above `nvm_ctrl_info_perms_set`.
void nvm_ctrl_info_cfg_lock(nvm_info_page_t page) {
  const rram_ctrl_info_page_t *p = page_ptr(page);
  if (p->emulated) {
    return;
  }
  rram_ctrl_info_cfg_lock(p);
}

void nvm_ctrl_data_region_protect(uint32_t region, uint32_t page_offset,
                                  uint32_t num_pages, nvm_page_perms_t perms,
                                  nvm_page_cfg_t cfg, hardened_bool_t lock) {
  rram_ctrl_data_region_protect(region, page_offset, num_pages,
                                perms_to_rram(perms), cfg_to_rram(cfg), lock);
}

void nvm_ctrl_bank_erase_perms_set(hardened_bool_t enable) {
  // RRAM has no bank-erase concept; nothing to permission-gate. The only
  // caller, `nvm_ctrl_chip_erase`, is itself a no-op for RRAM.
  (void)enable;
}

void nvm_ctrl_exec_set(uint32_t exec_val) { rram_ctrl_exec_set(exec_val); }

void nvm_ctrl_creator_info_pages_lockdown(void) {
  // Only 4 of the 7 pages below are real (non-emulated) RRAM info pages; see
  // the loop below and the TODO on `rram_ctrl_info_page_t`.
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kNvmCtrlSecMmioCreatorInfoPagesLockdown, 8);
  size_t i = 0, r = kNvmPagesNoOwnerAccessCount - 1;
  for (; launder32(i) < kNvmPagesNoOwnerAccessCount &&
         launder32(r) < kNvmPagesNoOwnerAccessCount;
       ++i, --r) {
    const rram_ctrl_info_page_t *p = page_ptr(kNvmPagesNoOwnerAccess[i]);
    // Of the 7 pages above, 3 (BootData0, BootData1, CreatorReserved0) are
    // emulated and share a memory-protection region with owner-needed pages
    // (OwnerSlot0/1, DiceCerts, ...); lockdown cannot revoke creator access
    // to an emulated page without also breaking owner access to the others
    // sharing its region. Known, accepted gap; see the TODO on
    // `rram_ctrl_info_page_t`. `kNvmCtrlSecMmioCreatorInfoPagesLockdown` is
    // tech-conditional in nvm_ctrl.h and already accounts for only the real
    // pages below being written.
    if (!p->emulated) {
      rram_ctrl_info_page_lockdown(p);
    }
  }
  HARDENED_CHECK_EQ(i, kNvmPagesNoOwnerAccessCount);
  HARDENED_CHECK_EQ(r, SIZE_MAX);
}

#else  // !HAS_RRAM_CTRL

void nvm_ctrl_init(void) { flash_ctrl_init(); }

void nvm_ctrl_disable(void) { flash_ctrl_disable(); }

rom_error_t nvm_ctrl_data_read(uint32_t addr, uint32_t word_count, void *data) {
  return flash_ctrl_data_read(addr, word_count, data);
}

rom_error_t nvm_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                const void *data) {
  return flash_ctrl_data_write(addr, word_count, data);
}

rom_error_t nvm_ctrl_data_erase(uint32_t addr) {
  return flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage);
}

rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr) {
  return flash_ctrl_data_erase_verify(addr, kFlashCtrlEraseTypePage);
}

rom_error_t nvm_ctrl_chip_erase(void) {
  flash_ctrl_bank_erase_perms_set(kHardenedBoolTrue);
  rom_error_t err_0 = flash_ctrl_data_erase(0, kFlashCtrlEraseTypeBank);
  rom_error_t err_1 = flash_ctrl_data_erase(FLASH_CTRL_PARAM_BYTES_PER_BANK,
                                            kFlashCtrlEraseTypeBank);
  flash_ctrl_bank_erase_perms_set(kHardenedBoolFalse);
  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

rom_error_t nvm_ctrl_chip_erase_verify(void) {
  rom_error_t err_0 = flash_ctrl_data_erase_verify(0, kFlashCtrlEraseTypeBank);
  rom_error_t err_1 = flash_ctrl_data_erase_verify(
      FLASH_CTRL_PARAM_BYTES_PER_BANK, kFlashCtrlEraseTypeBank);
  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

rom_error_t nvm_ctrl_page_program(uint32_t addr, size_t byte_count,
                                  uint8_t *data) {
  static_assert((FLASH_CTRL_PARAM_BYTES_PER_WORD &
                 (FLASH_CTRL_PARAM_BYTES_PER_WORD - 1)) == 0,
                "Bytes per NVM word must be a power of two.");
  enum {
    kWordMask = FLASH_CTRL_PARAM_BYTES_PER_WORD - 1,
    kProgPageSize = NVM_PROG_PAGE_SIZE,
    kProgPageMask = kProgPageSize - 1,
  };

  // Round up to next NVM word and fill missing bytes with 0xff.
  size_t word_misalignment = byte_count & kWordMask;
  if (word_misalignment > 0) {
    size_t pad = FLASH_CTRL_PARAM_BYTES_PER_WORD - word_misalignment;
    for (size_t i = 0; i < pad; ++i) {
      data[byte_count++] = 0xff;
    }
  }
  size_t rem_word_count = byte_count / sizeof(uint32_t);

  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4False,
  });
  // Split the write if addr is not `kProgPageSize`-aligned: first chunk fills
  // up to the page boundary, second chunk starts at the aligned address (SPI
  // PAGE_PROGRAM wrapping semantics).
  rom_error_t err_0 = kErrorOk;
  size_t prog_page_misalignment = addr & kProgPageMask;
  if (prog_page_misalignment > 0) {
    size_t word_count =
        (kProgPageSize - prog_page_misalignment) / sizeof(uint32_t);
    if (word_count > rem_word_count) {
      word_count = rem_word_count;
    }
    err_0 = flash_ctrl_data_write(addr, word_count, data);
    rem_word_count -= word_count;
    data += word_count * sizeof(uint32_t);
    addr &= ~(uint32_t)kProgPageMask;
  }
  rom_error_t err_1 = kErrorOk;
  if (rem_word_count > 0) {
    err_1 = flash_ctrl_data_write(addr, rem_word_count, data);
  }
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  });
  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

rom_error_t nvm_ctrl_sector_erase(uint32_t addr) {
  static_assert(FLASH_CTRL_PARAM_BYTES_PER_PAGE == 2048,
                "Page size must be 2 KiB");
  enum { kSectorAddrMask = ~UINT32_C(4096) + 1 };
  addr &= kSectorAddrMask;
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4True,
  });
  rom_error_t err_0 = flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage);
  rom_error_t err_1 = flash_ctrl_data_erase(
      addr + FLASH_CTRL_PARAM_BYTES_PER_PAGE, kFlashCtrlEraseTypePage);
  flash_ctrl_data_default_perms_set((flash_ctrl_perms_t){
      .read = kMultiBitBool4False,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  });
  HARDENED_RETURN_IF_ERROR(err_0);
  return err_1;
}

rom_error_t nvm_ctrl_info_read(nvm_info_page_t page, uint32_t offset,
                               uint32_t word_count, void *data) {
  return flash_ctrl_info_read(page_ptr(page), offset, word_count, data);
}

rom_error_t nvm_ctrl_info_read_zeros_on_read_error(nvm_info_page_t page,
                                                   uint32_t offset,
                                                   uint32_t word_count,
                                                   void *data) {
  return flash_ctrl_info_read_zeros_on_read_error(page_ptr(page), offset,
                                                  word_count, data);
}

rom_error_t nvm_ctrl_info_write(nvm_info_page_t page, uint32_t offset,
                                uint32_t word_count, const void *data) {
  return flash_ctrl_info_write(page_ptr(page), offset, word_count, data);
}

rom_error_t nvm_ctrl_info_erase(nvm_info_page_t page) {
  return flash_ctrl_info_erase(page_ptr(page), kFlashCtrlEraseTypePage);
}

void nvm_ctrl_data_default_perms_set(nvm_page_perms_t perms) {
  flash_ctrl_data_default_perms_set(perms_to_flash(perms));
}

void nvm_ctrl_info_perms_set(nvm_info_page_t page, nvm_page_perms_t perms) {
  flash_ctrl_info_perms_set(page_ptr(page), perms_to_flash(perms));
}

void nvm_ctrl_data_default_cfg_set(nvm_page_cfg_t cfg) {
  flash_ctrl_data_default_cfg_set(cfg_to_flash(cfg));
}

nvm_page_cfg_t nvm_ctrl_data_default_cfg_get(void) {
  return cfg_from_flash(flash_ctrl_data_default_cfg_get());
}

nvm_page_cfg_t nvm_ctrl_boot_data_cfg_get(void) {
  return cfg_from_flash(flash_ctrl_boot_data_cfg_get());
}

void nvm_ctrl_info_cfg_set(nvm_info_page_t page, nvm_page_cfg_t cfg) {
  flash_ctrl_info_cfg_set(page_ptr(page), cfg_to_flash(cfg));
}

void nvm_ctrl_info_cfg_lock(nvm_info_page_t page) {
  flash_ctrl_info_cfg_lock(page_ptr(page));
}

void nvm_ctrl_data_region_protect(uint32_t region, uint32_t page_offset,
                                  uint32_t num_pages, nvm_page_perms_t perms,
                                  nvm_page_cfg_t cfg, hardened_bool_t lock) {
  flash_ctrl_data_region_protect(region, page_offset, num_pages,
                                 perms_to_flash(perms), cfg_to_flash(cfg),
                                 lock);
}

void nvm_ctrl_bank_erase_perms_set(hardened_bool_t enable) {
  flash_ctrl_bank_erase_perms_set(enable);
}

void nvm_ctrl_exec_set(uint32_t exec_val) { flash_ctrl_exec_set(exec_val); }

void nvm_ctrl_creator_info_pages_lockdown(void) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kNvmCtrlSecMmioCreatorInfoPagesLockdown,
                                  2 * kNvmPagesNoOwnerAccessCount);
  size_t i = 0, r = kNvmPagesNoOwnerAccessCount - 1;
  for (; launder32(i) < kNvmPagesNoOwnerAccessCount &&
         launder32(r) < kNvmPagesNoOwnerAccessCount;
       ++i, --r) {
    flash_ctrl_info_page_lockdown(page_ptr(kNvmPagesNoOwnerAccess[i]));
  }
  HARDENED_CHECK_EQ(i, kNvmPagesNoOwnerAccessCount);
  HARDENED_CHECK_EQ(r, SIZE_MAX);
}

#endif  // HAS_RRAM_CTRL

void nvm_ctrl_cert_info_page_creator_cfg(nvm_info_page_t page) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kNvmCtrlSecMmioCertInfoPageCreatorCfg, 2);
  nvm_ctrl_info_cfg_set(page, kNvmCertInfoPageCfg);
  nvm_ctrl_info_perms_set(page, kNvmCertInfoPageCreatorAccess);
}

void nvm_ctrl_cert_info_page_owner_restrict(nvm_info_page_t page) {
  SEC_MMIO_ASSERT_WRITE_INCREMENT(kNvmCtrlSecMmioCertInfoPageOwnerRestrict, 2);
  nvm_ctrl_info_perms_set(page, kNvmCertInfoPageOwnerAccess);
  nvm_ctrl_info_cfg_lock(page);
}
