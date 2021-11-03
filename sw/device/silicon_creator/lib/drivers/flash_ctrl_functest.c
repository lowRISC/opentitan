// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig = {
    .can_clobber_uart = true,
};

const static uint32_t test_data[] = {
    0x52cdace1, 0xd0e94a26, 0xffc5ec40, 0xae30dabc, 0x753c881c, 0xe95f3bb6,
    0x794403bf, 0xa3aaeee9, 0x017bbde6, 0xeaf0b401, 0x46377cc2, 0xb013d410,
    0x8d5e176a, 0xcd2b1607, 0x0d0c76d3, 0xdfad0320, 0xcb306115, 0x5db81dda,
    0x4d469839, 0x56040fe1, 0x0e60181e, 0xa53b14d4, 0xe5306792, 0x26e973b5,
    0x50d167e4, 0x4ac2cb21, 0x8adb135e, 0x8e885b99, 0x3564bee5, 0x9f37838f,
    0x67c1e084, 0xc604492e, 0x0f59d183, 0xb49c5bd3, 0xdd65fed8, 0x01a62dce,
    0x9e5be9ee, 0x9869f1d0, 0x0b7702b8, 0xbda929bc, 0x1ea52ac2, 0x8212af95,
    0x42b45a40, 0x2ea7bc3c, 0x79e107ff, 0x8f4135b8, 0xe62774e0, 0xb518011f,
    0x8ad9ada5, 0xa0d3e958, 0x40eebd86, 0x3a3e86b1, 0x9a8c3bbc, 0x77ae968e,
    0xb26e4b40, 0xbab986d9, 0x47cbb266, 0xbfef01d3, 0x152997e8, 0xf71221d9,
    0x5342ee03, 0x8d183ba9, 0x4399ad8d, 0x9b7fb58e,
};

rom_error_t flash_ctrl_data_test(void) {
  uint32_t addr = FLASH_MEM_BASE_ADDR + 0x20000;

  // TODO Remove dependence on sw/device/lib/flash_ctrl once MP is added to ROM.
  mp_region_t cfg = {.num = 0,
                     .base = addr,
                     .size = ARRAYSIZE(test_data),
                     .part = kDataPartition,
                     .rd_en = true,
                     .prog_en = true,
                     .erase_en = true,
                     .scramble_en = false};
  flash_cfg_region(&cfg);
  RETURN_IF_ERROR(
      flash_ctrl_erase(addr, kFlashCtrlRegionData, kFlashCtrlErasePage));
  RETURN_IF_ERROR(flash_ctrl_prog(addr, ARRAYSIZE(test_data),
                                  kFlashCtrlRegionData, test_data));

  static uint32_t data_out[ARRAYSIZE(test_data)];
  RETURN_IF_ERROR(flash_ctrl_read(addr, ARRAYSIZE(test_data),
                                  kFlashCtrlRegionData, data_out));

  for (size_t i = 0; i < ARRAYSIZE(test_data); ++i) {
    if (data_out[i] != test_data[i]) {
      LOG_ERROR("FIFO data mismatch at 0x%08x, expected 0x%08x got 0x%08x.", i,
                test_data[i], data_out[i]);
      return kErrorUnknown;
    }

    uint32_t direct_read = abs_mmio_read32(addr + i * sizeof(uint32_t));
    if (direct_read != test_data[i]) {
      LOG_ERROR("Direct data mismatch at 0x%08x, expected 0x%08x got 0x%08x.",
                i, test_data[i], direct_read);
      return kErrorUnknown;
    }
  }

  return kErrorOk;
}

rom_error_t flash_ctrl_run_tests(void) {
  rom_error_t result = kErrorOk;
  EXECUTE_TEST(result, flash_ctrl_data_test);
  RETURN_IF_ERROR(result);
  return kErrorOk;
}

bool test_main(void) {
  rom_error_t result = flash_ctrl_run_tests();
  if (result == kErrorFlashCtrlInternal) {
    LOG_ERROR("Internal flash_ctrl error %x", flash_ctrl_read_internal_error());
  }
  return result == kErrorOk;
}
