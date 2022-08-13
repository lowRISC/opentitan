// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"

namespace rom_test {
extern "C" {

void flash_ctrl_init(void) { MockFlashCtrl::Instance().Init(); }

void flash_ctrl_status_get(flash_ctrl_status_t *status) {
  MockFlashCtrl::Instance().StatusGet(status);
}

rom_error_t flash_ctrl_data_read(uint32_t addr, uint32_t word_count,
                                 void *data) {
  return MockFlashCtrl::Instance().DataRead(addr, word_count, data);
}

rom_error_t flash_ctrl_info_read(flash_ctrl_info_page_t info_page,
                                 uint32_t offset, uint32_t word_count,
                                 void *data) {
  return MockFlashCtrl::Instance().InfoRead(info_page, offset, word_count,
                                            data);
}

rom_error_t flash_ctrl_data_write(uint32_t addr, uint32_t word_count,
                                  const void *data) {
  return MockFlashCtrl::Instance().DataWrite(addr, word_count, data);
}

rom_error_t flash_ctrl_info_write(flash_ctrl_info_page_t info_page,
                                  uint32_t offset, uint32_t word_count,
                                  const void *data) {
  return MockFlashCtrl::Instance().InfoWrite(info_page, offset, word_count,
                                             data);
}

rom_error_t flash_ctrl_data_erase(uint32_t addr,
                                  flash_ctrl_erase_type_t erase_type) {
  return MockFlashCtrl::Instance().DataErase(addr, erase_type);
}

rom_error_t flash_ctrl_data_erase_verify(uint32_t addr,
                                         flash_ctrl_erase_type_t erase_type) {
  return MockFlashCtrl::Instance().DataEraseVerify(addr, erase_type);
}

rom_error_t flash_ctrl_info_erase(flash_ctrl_info_page_t info_page,
                                  flash_ctrl_erase_type_t erase_type) {
  return MockFlashCtrl::Instance().InfoErase(info_page, erase_type);
}

void flash_ctrl_data_default_perms_set(flash_ctrl_perms_t perms) {
  MockFlashCtrl::Instance().DataDefaultPermsSet(perms);
}

void flash_ctrl_info_perms_set(flash_ctrl_info_page_t info_page,
                               flash_ctrl_perms_t perms) {
  MockFlashCtrl::Instance().InfoPermsSet(info_page, perms);
}

void flash_ctrl_data_default_cfg_set(flash_ctrl_cfg_t cfg) {
  MockFlashCtrl::Instance().DataDefaultCfgSet(cfg);
}

void flash_ctrl_info_cfg_set(flash_ctrl_info_page_t info_page,
                             flash_ctrl_cfg_t cfg) {
  MockFlashCtrl::Instance().InfoCfgSet(info_page, cfg);
}

void flash_ctrl_bank_erase_perms_set(hardened_bool_t enable) {
  MockFlashCtrl::Instance().BankErasePermsSet(enable);
}

void flash_ctrl_exec_set(uint32_t exec_val) {
  MockFlashCtrl::Instance().ExecSet(exec_val);
}

void flash_ctrl_creator_info_pages_lockdown(void) {
  MockFlashCtrl::Instance().CreatorInfoPagesLockdown();
}

}  // extern "C"
}  // namespace rom_test
