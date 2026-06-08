// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

// ---------------------------------------------------------------------------
// Static assertions: verify nvm_ctrl_erase_type_t values match the driver.
// ---------------------------------------------------------------------------
static_assert((uint32_t)kNvmCtrlEraseTypePage ==
                  (uint32_t)kFlashCtrlEraseTypePage,
              "erase type Page value mismatch");
static_assert((uint32_t)kNvmCtrlEraseTypeBank ==
                  (uint32_t)kFlashCtrlEraseTypeBank,
              "erase type Bank value mismatch");

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
      .read = p.read ? kMultiBitBool4True : kMultiBitBool4False,
      .write = p.write ? kMultiBitBool4True : kMultiBitBool4False,
      .erase = p.erase ? kMultiBitBool4True : kMultiBitBool4False,
  };
}

static flash_ctrl_cfg_t cfg_to_flash(nvm_page_cfg_t c) {
  return (flash_ctrl_cfg_t){
      .scrambling = c.scrambling ? kMultiBitBool4True : kMultiBitBool4False,
      .ecc = c.ecc ? kMultiBitBool4True : kMultiBitBool4False,
      .he = c.he ? kMultiBitBool4True : kMultiBitBool4False,
  };
}

static nvm_page_cfg_t cfg_from_flash(flash_ctrl_cfg_t c) {
  return (nvm_page_cfg_t){
      .scrambling = (c.scrambling == kMultiBitBool4True),
      .ecc = (c.ecc == kMultiBitBool4True),
      .he = (c.he == kMultiBitBool4True),
  };
}

// ---------------------------------------------------------------------------
// Named constants
// ---------------------------------------------------------------------------

const nvm_page_perms_t kNvmPagePermsReadWrite = {
    .read = true, .write = true, .erase = true};
const nvm_page_perms_t kNvmPagePermsReadOnly = {
    .read = true, .write = false, .erase = false};
const nvm_page_perms_t kNvmPagePermsNone = {
    .read = false, .write = false, .erase = false};

const nvm_page_cfg_t kNvmPageCfgScrambled = {
    .scrambling = true, .ecc = true, .he = false};
const nvm_page_cfg_t kNvmPageCfgPlain = {
    .scrambling = false, .ecc = true, .he = false};

const nvm_page_cfg_t kNvmCertInfoPageCfg = {
    .scrambling = true, .ecc = true, .he = false};
const nvm_page_perms_t kNvmCertInfoPageCreatorAccess = {
    .read = true, .write = true, .erase = true};
const nvm_page_perms_t kNvmCertInfoPageOwnerAccess = {
    .read = true, .write = false, .erase = false};

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

rom_error_t nvm_ctrl_data_erase(uint32_t addr,
                                nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_data_erase(addr, (flash_ctrl_erase_type_t)erase_type);
}

rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr,
                                       nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_data_erase_verify(addr,
                                      (flash_ctrl_erase_type_t)erase_type);
}

// ---------------------------------------------------------------------------
// Info page I/O
// ---------------------------------------------------------------------------

rom_error_t nvm_ctrl_info_read(nvm_info_page_t page, uint32_t offset,
                               uint32_t word_count, void *data) {
  return flash_ctrl_info_read(page_ptr(page), offset, word_count, data);
}

rom_error_t nvm_ctrl_info_read_zeros_on_error(nvm_info_page_t page,
                                              uint32_t offset,
                                              uint32_t word_count, void *data) {
  return flash_ctrl_info_read_zeros_on_read_error(page_ptr(page), offset,
                                                  word_count, data);
}

rom_error_t nvm_ctrl_info_write(nvm_info_page_t page, uint32_t offset,
                                uint32_t word_count, const void *data) {
  return flash_ctrl_info_write(page_ptr(page), offset, word_count, data);
}

rom_error_t nvm_ctrl_info_erase(nvm_info_page_t page,
                                nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_info_erase(page_ptr(page),
                               (flash_ctrl_erase_type_t)erase_type);
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

void nvm_ctrl_creator_info_pages_lockdown(void) {
  flash_ctrl_creator_info_pages_lockdown();
}

void nvm_ctrl_cert_info_page_creator_cfg(nvm_info_page_t page) {
  flash_ctrl_cert_info_page_creator_cfg(page_ptr(page));
}

void nvm_ctrl_cert_info_page_owner_restrict(nvm_info_page_t page) {
  flash_ctrl_cert_info_page_owner_restrict(page_ptr(page));
}
