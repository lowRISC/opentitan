// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/nvm_ctrl.h"

#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

// All functions forward to flash_ctrl.
// When moving to a different NVM technology, replace the bodies of these
// functions with calls to the new driver.

// ---------------------------------------------------------------------------
// Info page instances: re-export the flash_ctrl info page structs.
// ---------------------------------------------------------------------------

#define INFO_PAGE_NVM_CTRL_INST_(name_, bank_, page_) \
  const nvm_ctrl_info_page_t nvm_ctrl_##name_ = name_;

NVM_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_NVM_CTRL_INST_)
#undef INFO_PAGE_NVM_CTRL_INST_

// Certificate page configuration and permissions
const nvm_ctrl_cfg_t   kNvmCertificateInfoPageCfg           = kCertificateInfoPageCfg;
const nvm_ctrl_perms_t kNvmCertificateInfoPageCreatorAccess  = kCertificateInfoPageCreatorAccess;
const nvm_ctrl_perms_t kNvmCertificateInfoPageOwnerAccess    = kCertificateInfoPageOwnerAccess;

// ---------------------------------------------------------------------------
// Functions
// ---------------------------------------------------------------------------

void nvm_ctrl_init(void) { flash_ctrl_init(); }

void nvm_ctrl_disable(void) { flash_ctrl_disable(); }

void nvm_ctrl_status_get(nvm_ctrl_status_t *status) {
  flash_ctrl_status_get(status);
}

void nvm_ctrl_error_code_get(nvm_ctrl_error_code_t *error_code) {
  flash_ctrl_error_code_get(error_code);
}

rom_error_t nvm_ctrl_data_read(uint32_t addr, uint32_t word_count,
                                void *data) {
  return flash_ctrl_data_read(addr, word_count, data);
}

rom_error_t nvm_ctrl_info_read(const nvm_ctrl_info_page_t *info_page,
                                uint32_t offset, uint32_t word_count,
                                void *data) {
  return flash_ctrl_info_read(info_page, offset, word_count, data);
}

rom_error_t nvm_ctrl_info_read_zeros_on_read_error(
    const nvm_ctrl_info_page_t *info_page, uint32_t offset,
    uint32_t word_count, void *data) {
  return flash_ctrl_info_read_zeros_on_read_error(info_page, offset,
                                                   word_count, data);
}

rom_error_t nvm_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                 const void *data) {
  return flash_ctrl_data_write(addr, word_count, data);
}

rom_error_t nvm_ctrl_info_write(const nvm_ctrl_info_page_t *info_page,
                                 uint32_t offset, uint32_t word_count,
                                 const void *data) {
  return flash_ctrl_info_write(info_page, offset, word_count, data);
}

rom_error_t nvm_ctrl_data_erase(uint32_t addr,
                                 nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_data_erase(addr, erase_type);
}

rom_error_t nvm_ctrl_data_erase_verify(uint32_t addr,
                                        nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_data_erase_verify(addr, erase_type);
}

rom_error_t nvm_ctrl_info_erase(const nvm_ctrl_info_page_t *info_page,
                                 nvm_ctrl_erase_type_t erase_type) {
  return flash_ctrl_info_erase(info_page, erase_type);
}

void nvm_ctrl_data_default_perms_set(nvm_ctrl_perms_t perms) {
  flash_ctrl_data_default_perms_set(perms);
}

void nvm_ctrl_info_perms_set(const nvm_ctrl_info_page_t *info_page,
                              nvm_ctrl_perms_t perms) {
  flash_ctrl_info_perms_set(info_page, perms);
}

void nvm_ctrl_data_default_cfg_set(nvm_ctrl_cfg_t cfg) {
  flash_ctrl_data_default_cfg_set(cfg);
}

nvm_ctrl_cfg_t nvm_ctrl_data_default_cfg_get(void) {
  return flash_ctrl_data_default_cfg_get();
}

nvm_ctrl_cfg_t nvm_ctrl_boot_data_cfg_get(void) {
  return flash_ctrl_boot_data_cfg_get();
}

void nvm_ctrl_data_region_protect(nvm_ctrl_region_index_t region,
                                   uint32_t page_offset, uint32_t num_pages,
                                   nvm_ctrl_perms_t perms, nvm_ctrl_cfg_t cfg,
                                   hardened_bool_t lock) {
  flash_ctrl_data_region_protect(region, page_offset, num_pages, perms, cfg,
                                  lock);
}

void nvm_ctrl_info_cfg_set(const nvm_ctrl_info_page_t *info_page,
                            nvm_ctrl_cfg_t cfg) {
  flash_ctrl_info_cfg_set(info_page, cfg);
}

void nvm_ctrl_info_cfg_lock(const nvm_ctrl_info_page_t *info_page) {
  flash_ctrl_info_cfg_lock(info_page);
}

void nvm_ctrl_bank_erase_perms_set(hardened_bool_t enable) {
  flash_ctrl_bank_erase_perms_set(enable);
}

void nvm_ctrl_exec_set(uint32_t exec_val) { flash_ctrl_exec_set(exec_val); }

void nvm_ctrl_creator_info_pages_lockdown(void) {
  flash_ctrl_creator_info_pages_lockdown();
}

void nvm_ctrl_cert_info_page_creator_cfg(
    const nvm_ctrl_info_page_t *info_page) {
  flash_ctrl_cert_info_page_creator_cfg(info_page);
}

void nvm_ctrl_cert_info_page_owner_restrict(
    const nvm_ctrl_info_page_t *info_page) {
  flash_ctrl_cert_info_page_owner_restrict(info_page);
}

rom_error_t nvm_ctrl_info_type0_params_build(uint8_t bank, uint8_t page,
                                              nvm_ctrl_info_page_t *info_page) {
  return flash_ctrl_info_type0_params_build(bank, page, info_page);
}
