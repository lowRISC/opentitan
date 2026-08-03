// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_rram_ctrl.h"

namespace rom_test {
extern "C" {

void rram_ctrl_init(void) { MockRramCtrl::Instance().Init(); }

void rram_ctrl_disable(void) { MockRramCtrl::Instance().Disable(); }

void rram_ctrl_status_get(rram_ctrl_status_t *status) {
  MockRramCtrl::Instance().StatusGet(status);
}

void rram_ctrl_error_code_get(rram_ctrl_error_code_t *error_code) {
  MockRramCtrl::Instance().ErrorCodeGet(error_code);
}

rom_error_t rram_ctrl_data_read(uint32_t addr, uint32_t word_count,
                                void *data) {
  return MockRramCtrl::Instance().DataRead(addr, word_count, data);
}

rom_error_t rram_ctrl_info_read(const rram_ctrl_info_page_t *info_page,
                                uint32_t offset, uint32_t word_count,
                                void *data) {
  return MockRramCtrl::Instance().InfoRead(info_page, offset, word_count, data);
}

rom_error_t rram_ctrl_info_read_zeros_on_read_error(
    const rram_ctrl_info_page_t *info_page, uint32_t offset,
    uint32_t word_count, void *data) {
  return MockRramCtrl::Instance().InfoReadZerosOnReadError(info_page, offset,
                                                           word_count, data);
}

rom_error_t rram_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                 const void *data) {
  return MockRramCtrl::Instance().DataWrite(addr, word_count, data);
}

rom_error_t rram_ctrl_info_write(const rram_ctrl_info_page_t *info_page,
                                 uint32_t offset, uint32_t word_count,
                                 const void *data) {
  return MockRramCtrl::Instance().InfoWrite(info_page, offset, word_count,
                                            data);
}

void rram_ctrl_data_default_perms_set(rram_ctrl_perms_t perms) {
  MockRramCtrl::Instance().DataDefaultPermsSet(perms);
}

void rram_ctrl_info_perms_set(const rram_ctrl_info_page_t *info_page,
                              rram_ctrl_perms_t perms) {
  MockRramCtrl::Instance().InfoPermsSet(info_page, perms);
}

void rram_ctrl_data_default_cfg_set(rram_ctrl_cfg_t cfg) {
  MockRramCtrl::Instance().DataDefaultCfgSet(cfg);
}

rram_ctrl_cfg_t rram_ctrl_data_default_cfg_get() {
  return MockRramCtrl::Instance().DataDefaultCfgGet();
}

rram_ctrl_cfg_t rram_ctrl_boot_data_cfg_get() {
  return MockRramCtrl::Instance().BootDataCfgGet();
}

void rram_ctrl_info_cfg_set(const rram_ctrl_info_page_t *info_page,
                            rram_ctrl_cfg_t cfg) {
  MockRramCtrl::Instance().InfoCfgSet(info_page, cfg);
}

void rram_ctrl_info_cfg_lock(const rram_ctrl_info_page_t *info_page) {
  MockRramCtrl::Instance().InfoCfgLock(info_page);
}

void rram_ctrl_data_region_protect(rram_ctrl_region_index_t region,
                                   uint32_t page_offset, uint32_t num_pages,
                                   rram_ctrl_perms_t perms, rram_ctrl_cfg_t cfg,
                                   hardened_bool_t lock) {
  MockRramCtrl::Instance().DataRegionProtect(region, page_offset, num_pages,
                                             perms, cfg, lock);
}

void rram_ctrl_exec_set(uint32_t exec_val) {
  MockRramCtrl::Instance().ExecSet(exec_val);
}

void rram_ctrl_info_page_lockdown(const rram_ctrl_info_page_t *info_page) {
  MockRramCtrl::Instance().InfoPageLockdown(info_page);
}

}  // extern "C"
}  // namespace rom_test
