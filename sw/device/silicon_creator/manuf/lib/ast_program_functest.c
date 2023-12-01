// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

OTTF_DEFINE_TEST_CONFIG(.console.test_may_clobber = true);

// These symbols come from the `ast_program` module.
extern status_t ast_program_config(bool verbose);
extern status_t ast_program_init(bool verbose);
extern dif_flash_ctrl_state_t flash_state;

// Light-weight mocking: we export `ast_write` to the `ast_program` module so we
// can get a call for every word that would be written to AST.
uint32_t ast_crc;
uint32_t ast_nr_writes;
void ast_write(uint32_t addr, uint32_t data) {
  crc32_add32(&ast_crc, addr);
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
 *
 * @param data: The AST blob.  The format is <count> [<addr> <data> ...].
 */
static status_t program_page(const uint32_t *data) {
  dif_flash_ctrl_device_info_t device_info = dif_flash_ctrl_get_device_info();
  uint32_t byte_address =
      (kFlashInfoFieldAstCalibrationData.page * device_info.bytes_per_page) +
      kFlashInfoFieldAstCalibrationData.byte_offset;

  // The AST blob is 1 count word plus 2 additional words for every <count>.
  uint32_t size = (1 + data[0] * 2) * sizeof(uint32_t);
  return flash_ctrl_testutils_write(&flash_state, byte_address,
                                    kFlashInfoFieldAstCalibrationData.partition,
                                    data, kDifFlashCtrlPartitionTypeInfo, size);
}

/**
 * A fake AST configuration blob for testing.
 */
static const uint32_t sample_blob[] = {
    // The number of configuration pairs:
    4,
    // The config address/data pairs:
    0x40480000,
    0x1234,
    0x40480004,
    0x5678,
    0x40480008,
    0xabcd,
    0x4048000c,
    0xef00,
};

static status_t execute_test(void) {
  LOG_INFO("Initialize");
  TRY(ast_program_init(true));

  LOG_INFO("Erase the INFO page. Verify no AST programming; expect error.");
  test_state_reset();
  TRY(erase_page());
  TRY_CHECK(status_err(ast_program_config(true)));
  TRY_CHECK(ast_nr_writes == 0);

  LOG_INFO(
      "Program a sample blob into the INFO page.  Verify AST programming.");
  test_state_reset();
  TRY(program_page(sample_blob));
  TRY(ast_program_config(true));
  uint32_t crc = crc32(&sample_blob[1], sizeof(sample_blob) - sizeof(uint32_t));
  TRY_CHECK(ast_nr_writes == 4);
  TRY_CHECK(crc32_finish(&ast_crc) == crc);
  return OK_STATUS();
}

bool test_main(void) {
  // Run once just to get the flash controller initialzed.
  status_t sts = execute_test();
  LOG_INFO("result = %r", sts);
  return status_ok(sts);
}
