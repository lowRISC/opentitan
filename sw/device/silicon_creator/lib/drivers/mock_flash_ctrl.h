// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_

#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

namespace mask_rom_test {
namespace internal {

/**
 * Mock class for flash_ctrl.
 */
class MockFlashCtrl : public global_mock::GlobalMock<MockFlashCtrl> {
 public:
  MOCK_METHOD(void, Init, ());
  MOCK_METHOD(void, StatusGet, (flash_ctrl_status_t *));
  MOCK_METHOD(rom_error_t, DataRead, (uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, InfoRead,
              (flash_ctrl_info_page_t, uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, DataWrite, (uint32_t, uint32_t, const void *));
  MOCK_METHOD(rom_error_t, InfoWrite,
              (flash_ctrl_info_page_t, uint32_t, uint32_t, const void *));
  MOCK_METHOD(rom_error_t, DataErase, (uint32_t, flash_ctrl_erase_type_t));
  MOCK_METHOD(rom_error_t, DataEraseVerify,
              (uint32_t, flash_ctrl_erase_type_t));
  MOCK_METHOD(rom_error_t, InfoErase,
              (flash_ctrl_info_page_t, flash_ctrl_erase_type_t));
  MOCK_METHOD(void, DataDefaultPermsSet, (flash_ctrl_perms_t));
  MOCK_METHOD(void, InfoPermsSet, (flash_ctrl_info_page_t, flash_ctrl_perms_t));
  MOCK_METHOD(void, DataDefaultCfgSet, (flash_ctrl_cfg_t));
  MOCK_METHOD(void, InfoCfgSet, (flash_ctrl_info_page_t, flash_ctrl_cfg_t));
  MOCK_METHOD(void, BankErasePermsSet, (hardened_bool_t));
  MOCK_METHOD(void, ExecSet, (uint32_t));
  MOCK_METHOD(void, CreatorInfoPagesLockdown, ());
};

}  // namespace internal

using MockFlashCtrl = testing::StrictMock<internal::MockFlashCtrl>;

#ifdef IS_MESON_FOR_MIGRATIONS_ONLY
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
#endif
}  // namespace mask_rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_
