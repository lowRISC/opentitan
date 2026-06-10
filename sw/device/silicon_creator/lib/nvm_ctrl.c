// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

// ---------------------------------------------------------------------------
// Internal: info page count per bank in the type-0 info partition.
// ---------------------------------------------------------------------------
enum { kNvmInfoPagesPerBank = 10 };

// ---------------------------------------------------------------------------
// Internal: mapping from nvm_info_page_t enum to flash_ctrl page pointer.
// Order must match nvm_info_page_t definition in nvm_ctrl.h.
// ---------------------------------------------------------------------------
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

static_assert(ARRAYSIZE(kPageTable) == NVM_NUM_BANKS * kNvmInfoPagesPerBank,
              "kPageTable size does not match NVM_NUM_BANKS * pages per bank");

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

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

const nvm_page_cfg_t kNvmPageCfgScrambled = {.scrambling = kMultiBitBool4True,
                                             .ecc = kMultiBitBool4True,
                                             .he = kMultiBitBool4False};
const nvm_page_cfg_t kNvmPageCfgPlain = {.scrambling = kMultiBitBool4False,
                                         .ecc = kMultiBitBool4True,
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
// Lifecycle
// ---------------------------------------------------------------------------

void nvm_ctrl_init(void) { flash_ctrl_init(); }
void nvm_ctrl_disable(void) { flash_ctrl_disable(); }

// ---------------------------------------------------------------------------
// Wire-format bridge
// ---------------------------------------------------------------------------

rom_error_t nvm_ctrl_info_page_lookup(uint8_t bank, uint8_t page,
                                      nvm_info_page_t *out) {
  if ((uint32_t)bank >= (uint32_t)NVM_NUM_BANKS ||
      (uint32_t)page >= (uint32_t)kNvmInfoPagesPerBank) {
    return kErrorNvmCtrlInvalidInfoPage;
  }
  *out = (nvm_info_page_t)(bank * kNvmInfoPagesPerBank + page);
  return kErrorOk;
}

// ---------------------------------------------------------------------------
// Data partition I/O
// ---------------------------------------------------------------------------

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
    kProgPageSize = 256,
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
  // Split the write if addr is not 256-byte aligned: first chunk fills up to
  // the 256-byte boundary, second chunk starts at the aligned address (SPI
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

// ---------------------------------------------------------------------------
// Info page I/O
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Permissions and configuration
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Data region protection
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Lockdown and certificate page management
// ---------------------------------------------------------------------------

static const nvm_info_page_t kNvmPagesNoOwnerAccess[] = {
    kNvmInfoPageFactoryId,        kNvmInfoPageCreatorSecret,
    kNvmInfoPageOwnerSecret,      kNvmInfoPageWaferAuthSecret,
    kNvmInfoPageBootData0,        kNvmInfoPageBootData1,
    kNvmInfoPageCreatorReserved0,
};

enum {
  kNvmPagesNoOwnerAccessCount = ARRAYSIZE(kNvmPagesNoOwnerAccess),
};

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
