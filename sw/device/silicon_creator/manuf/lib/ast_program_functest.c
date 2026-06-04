// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"

OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

static uint32_t ast_cfg_data[kNvmInfoAstCalibrationDataSizeIn32BitWords] = {0};

// These symbols come from the `ast_program` module.
extern status_t ast_program_config(bool verbose);
extern status_t ast_program_init(bool verbose);

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
 * Erase the AST calibration info page and program a test blob into it.
 */
static status_t erase_and_program_page(void) {
  // Set dummy AST values for testing.
  for (size_t i = 0; i < ARRAYSIZE(ast_cfg_data); ++i) {
    ast_cfg_data[i] = i;
  }

  return nvm_testutils_write_info_page(
      kNvmInfoFieldAstCalibrationData.page,
      kNvmInfoFieldAstCalibrationData.byte_offset, ast_cfg_data,
      kNvmInfoAstCalibrationDataSizeIn32BitWords, /*scramble=*/false,
      /*erase_before_write=*/true);
}

static status_t execute_test(void) {
  LOG_INFO("Initialize");
  TRY(ast_program_init(true));
  LOG_INFO(
      "Erase and program a sample blob into the INFO page, and verify AST "
      "programming.");
  test_state_reset();
  TRY(erase_and_program_page());
  TRY(ast_program_config(true));
  uint32_t crc =
      crc32(ast_cfg_data, (kNvmInfoAstCalibrationDataSizeIn32BitWords - 3) *
                              sizeof(uint32_t));
  TRY_CHECK(ast_nr_writes == kFlashInfoAstCalibrationDataSizeIn32BitWords - 3);
  TRY_CHECK(crc32_finish(&ast_crc) == crc);
  return OK_STATUS();
}

bool test_main(void) {
  // Run once just to get the flash controller initialzed.
  status_t sts = execute_test();
  LOG_INFO("result = %r", sts);
  return status_ok(sts);
}
