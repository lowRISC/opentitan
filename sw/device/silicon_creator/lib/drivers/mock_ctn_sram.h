// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_CTN_SRAM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_CTN_SRAM_H_

#include "sw/device/silicon_creator/lib/drivers/ctn_sram.h"
#include "sw/lib/sw/device/base/global_mock.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for ctn_sram.c.
 */
class MockCtnSram : public global_mock::GlobalMock<MockCtnSram> {
 public:
  MOCK_METHOD(rom_error_t, DataWrite, (uint32_t, uint32_t, const void *));
  MOCK_METHOD(rom_error_t, DataErase, (uint32_t, ctn_sram_erase_type_t));
  MOCK_METHOD(rom_error_t, DataEraseVerify, (uint32_t, ctn_sram_erase_type_t));
  MOCK_METHOD(void, DataDefaultPermsSet, (ctn_sram_perms_t));
  MOCK_METHOD(void, BankErasePermsSet, (hardened_bool_t));
};

}  // namespace internal

using MockCtnSram = testing::StrictMock<internal::MockCtnSram>;

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_CTN_SRAM_H_
