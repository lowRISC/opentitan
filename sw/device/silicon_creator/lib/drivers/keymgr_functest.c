// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/silicon_creator/lib/base/abs_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"

#define ASSERT_OK(expr_)                        \
  do {                                          \
    rom_error_t local_error_ = expr_;           \
    if (local_error_ != kErrorOk) {             \
      LOG_ERROR("Error at line: %d", __LINE__); \
      return local_error_;                      \
    }                                           \
  } while (0)

#define ASSERT_EQZ(x) CHECK((x) == 0)

enum {
  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  /** Owner Secret flash info page ID. */
  kFlashInfoPageIdOwnerSecret = 2,

  /** Key manager secret word size. */
  kSecretWordSize = 16,
};

/**
 * Software binding value associated with the ROM_EXT. Programmed by
 * mask ROM.
 */
const keymgr_binding_value_t kBindingValueRomExt = {
    .data = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2, 0xb8a8379d,
             0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
};

/**
 * Software binding value associated with BL0. Programmed by ROM_EXT.
 */
const keymgr_binding_value_t kBindingValueBl0 = {
    .data = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa, 0x23fb480c,
             0xb012ae5e, 0xf1394d28, 0x1940ceeb},
};

/**
 * Key manager Creator Secret stored in info flash page.
 */
const uint32_t kCreatorSecret[kSecretWordSize] = {
    0x4e919d54, 0x322288d8, 0x4bd127c7, 0x9f89bc56, 0xb4fb0fdf, 0x1ca1567b,
    0x13a0e876, 0xa6521d8f, 0xbebf6301, 0xd10879a1, 0x69797afb, 0x5f295405,
    0x444a8511, 0xe7bb2fa5, 0xd570c0a3, 0xf15f82e5,
};

/**
 * Key manager Owner Secret stored in info flash page.
 */
const uint32_t kOwnerSecret[kSecretWordSize] = {
    0xf15f82e5, 0xd570c0a3, 0xe7bb2fa5, 0x444a8511, 0x5f295405, 0x69797afb,
    0xd10879a1, 0xbebf6301, 0xa6521d8f, 0x13a0e876, 0x1ca1567b, 0xb4fb0fdf,
    0x9f89bc56, 0x4bd127c7, 0x322288d8, 0x4e919d54,
};

/** ROM_EXT key manager maximum version. */
const uint32_t kMaxVerRomExt = 1;

/** BL0 key manager maximum version. */
const uint32_t kMaxVerBl0 = 2;

const test_config_t kTestConfig;

/**
 * Writes `size` words of `data` into flash info page.
 *
 * @param page_id Info page ID to write to.
 * @param data Data to write.
 * @param size Number of 4B words to write from `data` buffer.
 */
static void write_info_page(uint32_t page_id, const uint32_t *data,
                            size_t size) {
  mp_region_t info_region = {.num = page_id,
                             .base = 0x0,  // only used to calculate bank id.
                             .size = 0x1,  // unused for info pages.
                             .part = kInfoPartition,
                             .rd_en = true,
                             .prog_en = true,
                             .erase_en = true,
                             .scramble_en = false};
  flash_cfg_region(&info_region);

  uint32_t address = FLASH_MEM_BASE_ADDR + page_id * flash_get_page_size();

  ASSERT_EQZ(flash_page_erase(address, kInfoPartition));
  ASSERT_EQZ(flash_write(address, kInfoPartition, data, size));

  for (size_t i = 0; i < size; ++i) {
    uint32_t got_data;
    ASSERT_EQZ(flash_read(address + i * sizeof(uint32_t), kInfoPartition,
                          /*size=*/1, &got_data));
    CHECK(got_data == data[i]);
  }
  info_region.rd_en = false;
  info_region.prog_en = false;
  info_region.erase_en = false;
  flash_cfg_region(&info_region);
}

static void init_flash(void) {
  // setup default access for data partition
  flash_default_region_access(/*rd_en=*/true, /*prog_en=*/true,
                              /*erase_en=*/true);
  // Initialize flash secrets.
  write_info_page(kFlashInfoPageIdCreatorSecret, kCreatorSecret,
                  ARRAYSIZE(kCreatorSecret));
  write_info_page(kFlashInfoPageIdOwnerSecret, kOwnerSecret,
                  ARRAYSIZE(kOwnerSecret));
}

/** Key manager configuration steps performed in mask ROM. */
rom_error_t keymgr_rom_test(void) {
  ASSERT_OK(keymgr_check_state(kKeymgrStateReset));
  keymgr_set_next_stage_inputs(&kBindingValueRomExt, kMaxVerRomExt);
  return kErrorOk;
}

/** Key manager configuration steps performed in ROM_EXT. */
rom_error_t keymgr_rom_ext_test(void) {
  ASSERT_OK(keymgr_check_state(kKeymgrStateReset));

  const uint16_t kEntropyReseedInterval = 0x1234;
  ASSERT_OK(keymgr_init(kEntropyReseedInterval));
  keymgr_advance_state();
  ASSERT_OK(keymgr_check_state(kKeymgrStateInit));

  // FIXME: Check `kBindingValueRomExt` before advancing state.
  keymgr_advance_state();
  ASSERT_OK(keymgr_check_state(kKeymgrStateCreatorRootKey));

  keymgr_set_next_stage_inputs(&kBindingValueBl0, kMaxVerBl0);

  // FIXME: Check `kBindingValueBl0` before advancing state.
  keymgr_advance_state();
  ASSERT_OK(keymgr_check_state(kKeymgrStateOwnerIntermediateKey));
  return kErrorOk;
}

bool test_main(void) {
  rom_error_t result = kErrorOk;

  // This test is expected to run in DEV, PROD or PROD_END states.
  lifecycle_state_t lc_state = lifecycle_state_get();
  LOG_INFO("lifecycle state: %s", lifecycle_state_name[lc_state]);

  init_flash();

  EXECUTE_TEST(result, keymgr_rom_test);
  EXECUTE_TEST(result, keymgr_rom_ext_test);
  return result == kErrorOk;
}
