// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kNewMinSecVer = 1,
  kFlashCounterId = 0,
};

static void print_boot_data(const boot_data_t *boot_data) {
  LOG_INFO("counter: %d, min_security_version_rom_ext: %d", boot_data->counter,
           boot_data->min_security_version_rom_ext);
}

static void increment_flash_counter(void) {
  dif_flash_ctrl_state_t flash_ctrl;
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
      &flash_ctrl,
      /*rd_en*/ true,
      /*prog_en*/ true, false, false, false, false));
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_increment(&flash_ctrl, kFlashCounterId));
  CHECK_STATUS_OK(flash_ctrl_testutils_default_region_access(
      &flash_ctrl, false, false, false, false, false, false));
}

static rom_error_t first_boot_test(void) {
  LOG_INFO("First boot: interrupted upgrade");
  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  print_boot_data(&boot_data);
  CHECK(boot_data.min_security_version_rom_ext == 0);

  boot_data.min_security_version_rom_ext = kNewMinSecVer;
  RETURN_IF_ERROR(boot_data_write(&boot_data));
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  print_boot_data(&boot_data);
  CHECK(boot_data.min_security_version_rom_ext == kNewMinSecVer);

  uint32_t corrupted_words[4] = {0};
  flash_ctrl_info_perms_set(kFlashCtrlInfoPageBootData0,
                            (flash_ctrl_perms_t){
                                .read = kMultiBitBool4False,
                                .write = kMultiBitBool4True,
                                .erase = kMultiBitBool4False,
                            });
  RETURN_IF_ERROR(flash_ctrl_info_write(kFlashCtrlInfoPageBootData0, 0, 4,
                                        &corrupted_words));
  flash_ctrl_info_perms_set(kFlashCtrlInfoPageBootData0,
                            (flash_ctrl_perms_t){
                                .read = kMultiBitBool4False,
                                .write = kMultiBitBool4False,
                                .erase = kMultiBitBool4False,
                            });
  return kErrorOk;
}

static rom_error_t second_boot_test(void) {
  LOG_INFO("Second boot: Recovery");

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  print_boot_data(&boot_data);
  CHECK(boot_data.min_security_version_rom_ext == 0);

  boot_data.min_security_version_rom_ext = kNewMinSecVer;
  RETURN_IF_ERROR(boot_data_write(&boot_data));
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  print_boot_data(&boot_data);
  CHECK(boot_data.min_security_version_rom_ext == kNewMinSecVer);

  return kErrorOk;
}

static rom_error_t third_boot_test(void) {
  LOG_INFO("Third boot: Done");

  boot_data_t boot_data;
  RETURN_IF_ERROR(boot_data_read(lifecycle_state_get(), &boot_data));
  print_boot_data(&boot_data);
  CHECK(boot_data.min_security_version_rom_ext == kNewMinSecVer);

  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  size_t reboot_counter = 0;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_counter_get(kFlashCounterId, &reboot_counter));

  switch (reboot_counter) {
    case 0: {
      const manifest_t *manifest = manifest_def_get();
      LOG_INFO("Manifest security version: %d", manifest->security_version);
      CHECK(manifest->security_version > kNewMinSecVer);

      EXECUTE_TEST(result, first_boot_test);

      increment_flash_counter();
      rstmgr_reset();
      return false;
    }
    case 1: {
      EXECUTE_TEST(result, second_boot_test);

      increment_flash_counter();
      rstmgr_reset();
      return false;
    }
    case 2: {
      EXECUTE_TEST(result, third_boot_test);

      return status_ok(result);
    }
  }
  return false;
}
