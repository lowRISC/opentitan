// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/mock_ctn_sram.h"

namespace rom_test {
extern "C" {

rom_error_t ctn_sram_data_write(uint32_t addr, uint32_t len, const void *data) {
  return MockCtnSram::Instance().DataWrite(addr, len, data);
}

rom_error_t ctn_sram_data_erase(uint32_t addr,
                                ctn_sram_erase_type_t erase_type) {
  return MockCtnSram::Instance().DataErase(addr, erase_type);
}

rom_error_t ctn_sram_data_erase_verify(uint32_t addr,
                                       ctn_sram_erase_type_t erase_type) {
  return MockCtnSram::Instance().DataEraseVerify(addr, erase_type);
}

void ctn_sram_data_default_perms_set(ctn_sram_perms_t perms) {
  MockCtnSram::Instance().DataDefaultPermsSet(perms);
}

void ctn_sram_bank_erase_perms_set(hardened_bool_t enable) {
  MockCtnSram::Instance().BankErasePermsSet(enable);
}

}  // extern "C"
}  // namespace rom_test
