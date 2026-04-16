// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

#define CMD_EXECUTE 0xd8
#define CMD_SEC_WIPE_DMEM 0xc3

OTTF_DEFINE_TEST_CONFIG();

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

  // App range check (imem_end comes before imem_start)
  static const uint32_t kDummyMem[] = {0};
  otbn_app_t bad_range_app = {.imem_start = kDummyMem + 1,
                              .imem_end = kDummyMem,  // Backwards!
                              .dmem_data_start = kDummyMem,
                              .dmem_data_end = kDummyMem,
                              .dmem_data_start_addr = 0,
                              .checksum = 0};
  CHECK(otbn_load_app(bad_range_app).value == OTCRYPTO_BAD_ARGS.value);

  // Force OTBN out of the IDLE state by manually triggering a Secure Wipe.
  abs_mmio_write32(TOP_EARLGREY_OTBN_BASE_ADDR + OTBN_CMD_REG_OFFSET,
                   CMD_SEC_WIPE_DMEM);
  CHECK(otbn_execute().value == OTCRYPTO_ASYNC_INCOMPLETE.value);
  CHECK(otbn_busy_wait_for_done().value == OTCRYPTO_OK.value);

  // Test otbn_set_ctrl_software_errs_fatal()
  CHECK(otbn_set_ctrl_software_errs_fatal(false).value == OTCRYPTO_OK.value);
  CHECK(otbn_set_ctrl_software_errs_fatal(true).value == OTCRYPTO_OK.value);
  CHECK(otbn_set_ctrl_software_errs_fatal(false).value == OTCRYPTO_OK.value);

  // 6. Test bad checksum
  otbn_app_t bad_checksum_app = {.imem_start = kDummyMem,
                                 .imem_end = kDummyMem + 1,
                                 .dmem_data_start = kDummyMem,
                                 .dmem_data_end = kDummyMem + 1,
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
