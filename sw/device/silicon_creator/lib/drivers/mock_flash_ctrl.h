// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_

#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

namespace rom_test {
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
              (const flash_ctrl_info_page_t *, uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, DataWrite, (uint32_t, uint32_t, const void *));
  MOCK_METHOD(rom_error_t, InfoWrite,
              (const flash_ctrl_info_page_t *, uint32_t, uint32_t,
               const void *));
  MOCK_METHOD(rom_error_t, DataErase, (uint32_t, flash_ctrl_erase_type_t));
  MOCK_METHOD(rom_error_t, DataEraseVerify,
              (uint32_t, flash_ctrl_erase_type_t));
  MOCK_METHOD(rom_error_t, InfoErase,
              (const flash_ctrl_info_page_t *, flash_ctrl_erase_type_t));
  MOCK_METHOD(void, DataDefaultPermsSet, (flash_ctrl_perms_t));
  MOCK_METHOD(void, InfoPermsSet,
              (const flash_ctrl_info_page_t *, flash_ctrl_perms_t));
  MOCK_METHOD(flash_ctrl_cfg_t, DataDefaultCfgGet, ());
  MOCK_METHOD(void, DataDefaultCfgSet, (flash_ctrl_cfg_t));
  MOCK_METHOD(void, DataRegionProtect,
              (flash_ctrl_region_index_t region, uint32_t page_offset,
               uint32_t num_pages, flash_ctrl_perms_t perms,
               flash_ctrl_cfg_t cfg));
  MOCK_METHOD(void, InfoCfgSet,
              (const flash_ctrl_info_page_t *, flash_ctrl_cfg_t));
  MOCK_METHOD(void, BankErasePermsSet, (hardened_bool_t));
  MOCK_METHOD(void, ExecSet, (uint32_t));
  MOCK_METHOD(void, CreatorInfoPagesLockdown, ());
};

}  // namespace internal

using MockFlashCtrl = testing::StrictMock<internal::MockFlashCtrl>;
using NiceMockFlashCtrl = testing::NiceMock<internal::MockFlashCtrl>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_FLASH_CTRL_H_
