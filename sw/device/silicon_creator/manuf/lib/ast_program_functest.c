// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

static uint32_t ast_cfg_data[kFlashInfoAstCalibrationDataSizeIn32BitWords] = {
    0};

// These symbols come from the `ast_program` module.
extern status_t ast_program_config(bool verbose);
extern status_t ast_program_init(bool verbose);
extern dif_flash_ctrl_state_t flash_state;

// Light-weight mocking: we export `ast_write` to the `ast_program` module so we
// can get a call for every word that would be written to AST.
uint32_t ast_crc;
uint32_t ast_nr_writes;
void ast_write(uint32_t addr, uint32_t data) {
  crc32_add32(&ast_crc, data);
  ast_nr_writes += 1;
}

/**
 * Reset the CRC and count between tests.
 */
static void test_state_reset(void) {
  ast_nr_writes = 0;
  crc32_init(&ast_crc);
}

/**
 * Erase the INFO page containing the AST calibration data.
 */
static status_t erase_page(void) {
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (kFlashInfoFieldAstCalibrationData.page * device_info.bytes_per_page);

  return flash_ctrl_testutils_erase_page(
      &flash_state, byte_address, kFlashInfoFieldAstCalibrationData.partition,
      kDifFlashCtrlPartitionTypeInfo);
}

/**
 * Program a blob into the AST calibration info page.
 */
static status_t program_page(void) {
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (kFlashInfoFieldAstCalibrationData.page * device_info.bytes_per_page) +
      kFlashInfoFieldAstCalibrationData.byte_offset;

  // Set dummy AST values for testing.
  for (size_t i = 0; i < ARRAYSIZE(ast_cfg_data); ++i) {
    ast_cfg_data[i] = i;
  }
  return flash_ctrl_testutils_write(
      &flash_state, byte_address, kFlashInfoFieldAstCalibrationData.partition,
      ast_cfg_data, kDifFlashCtrlPartitionTypeInfo,
      kFlashInfoAstCalibrationDataSizeIn32BitWords);
}

static status_t execute_test(void) {
  LOG_INFO("Initialize");
  TRY(ast_program_init(true));
  LOG_INFO(
      "Erase and program a sample blob into the INFO page, and verify AST "
      "programming.");
  TRY(erase_page());
  test_state_reset();
  TRY(program_page());
  TRY(ast_program_config(true));
  uint32_t crc =
      crc32(ast_cfg_data,
            kFlashInfoAstCalibrationDataSizeIn32BitWords * sizeof(uint32_t));
  TRY_CHECK(ast_nr_writes == 39);
  TRY_CHECK(crc32_finish(&ast_crc) == crc);
  return OK_STATUS();
}

bool test_main(void) {
  // Run once just to get the flash controller initialzed.
  status_t sts = execute_test();
  LOG_INFO("result = %r", sts);
  return status_ok(sts);
}
