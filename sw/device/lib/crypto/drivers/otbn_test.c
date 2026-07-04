// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "hw/top/dt/otbn.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/otbn_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

#define CMD_EXECUTE 0xd8
#define CMD_SEC_WIPE_DMEM 0xc3

OTTF_DEFINE_TEST_CONFIG();

static const dt_otbn_t kOtbnDt = kDtOtbn;

static inline uint32_t otbn_base(void) {
  return dt_otbn_primary_reg_block(kOtbnDt);
}

static status_t dummy_wipe_dmem_macro_test(void) {
  HARDENED_TRY_WIPE_DMEM((status_t){.value = OTCRYPTO_BAD_ARGS.value});

  return OTCRYPTO_OK;
}

static status_t run_negative_test(void) {
  LOG_INFO("Running negative tests.");

  // Negative test HARDENED_TRY_WIPE_DMEM
  status_t wipe_res = dummy_wipe_dmem_macro_test();
  CHECK(status_err(wipe_res) == kInvalidArgument);

  // Test memory boundary check (offset + length exceeds memory)
  CHECK(otbn_dmem_read(0xFFFFFFFF, 0, NULL).value == OTCRYPTO_BAD_ARGS.value);

  // Dummy byte array for testing invalid pointers
  static const uint8_t kDummyMem[] = {0};

  // App range check (imem_compressed_end comes before imem_compressed_start)
  otbn_app_t bad_range_app = {.imem_compressed_start = kDummyMem + 1,
                              .imem_compressed_end = kDummyMem,  // Backwards!
                              .imem_uncompressed_words = 1,
                              .dmem_compressed_start = kDummyMem,
                              .dmem_compressed_end = kDummyMem,
                              .dmem_uncompressed_words = 0,
                              .dmem_data_start_addr = 0,
                              .checksum = 0};
  CHECK(otbn_load_app(bad_range_app).value == OTCRYPTO_BAD_ARGS.value);

  // App range check (imem uncompressed size is 0 - not allowed)
  otbn_app_t empty_imem_app = {.imem_compressed_start = kDummyMem,
                               .imem_compressed_end = kDummyMem + 1,
                               .imem_uncompressed_words = 0,  // Empty!
                               .dmem_compressed_start = kDummyMem,
                               .dmem_compressed_end = kDummyMem,
                               .dmem_uncompressed_words = 0,
                               .dmem_data_start_addr = 0,
                               .checksum = 0};
  CHECK(otbn_load_app(empty_imem_app).value == OTCRYPTO_BAD_ARGS.value);

  // Force OTBN out of the IDLE state by manually triggering a Secure Wipe.
  abs_mmio_write32(otbn_base() + OTBN_CMD_REG_OFFSET, CMD_SEC_WIPE_DMEM);
  CHECK(otbn_execute().value == OTCRYPTO_ASYNC_INCOMPLETE.value);
  CHECK(otbn_busy_wait_for_done().value == OTCRYPTO_OK.value);

  // Test otbn_set_ctrl_software_errs_fatal()
  CHECK(otbn_set_ctrl_software_errs_fatal(false).value == OTCRYPTO_OK.value);
  CHECK(otbn_set_ctrl_software_errs_fatal(true).value == OTCRYPTO_OK.value);
  CHECK(otbn_set_ctrl_software_errs_fatal(false).value == OTCRYPTO_OK.value);

  // Test bad checksum
  // We provide a tiny valid compressed block (0x40 = 4 literals, followed by
  // four 0x00 bytes) so decompression succeeds, ensuring we actually hit the
  // checksum verification failure.
  static const uint8_t kValidLz4[] = {0x40, 0x00, 0x00, 0x00, 0x00};

  otbn_app_t bad_checksum_app = {
      .imem_compressed_start = kValidLz4,
      .imem_compressed_end = kValidLz4 + sizeof(kValidLz4),
      .imem_uncompressed_words = 1,
      .dmem_compressed_start = kDummyMem,
      .dmem_compressed_end = kDummyMem,
      .dmem_uncompressed_words = 0,
      .dmem_data_start_addr = 0,
      .checksum = 0xDEADBEEF};
  CHECK(otbn_load_app(bad_checksum_app).value == OTCRYPTO_FATAL_ERR.value);

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(entropy_complex_init(kHardenedBoolFalse));

  EXECUTE_TEST(result, run_negative_test);

  return status_ok(result);
}
