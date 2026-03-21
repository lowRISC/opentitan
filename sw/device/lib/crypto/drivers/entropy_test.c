// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/crypto/drivers/entropy.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy_kat.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

#include "csrng_regs.h"
#include "edn_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('e', 'n', 't')

OTTF_DEFINE_TEST_CONFIG();

static status_t entropy_complex_init_test(void) {
  TRY(entropy_complex_init());

  // Check the configuration.
  TRY(entropy_complex_check());

  // The following test requests entropy from both EDN0 and EDN1.
  dif_otbn_t otbn;
  TRY_CHECK(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
                          &otbn) == kDifOk);
  otbn_randomness_test_start(&otbn, /*iters=*/0);
  TRY_CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_don_check=*/false));
  return OK_STATUS();
}

static status_t run_negative_test(void) {
  LOG_INFO("Running negative tests.");

  // Test too large length outputs
  CHECK(entropy_csrng_generate_start(NULL, 0x2001).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test too large seed material lengths
  entropy_seed_material_t bad_len_seed = {.len = 16, .data = {0}};
  CHECK(entropy_csrng_update(&bad_len_seed).value == OTCRYPTO_RECOV_ERR.value);

  // Test entropy_complex_check with a disabled CSRNG
  uint32_t csrng_ctrl_addr =
      TOP_EARLGREY_CSRNG_BASE_ADDR + CSRNG_CTRL_REG_OFFSET;
  uint32_t old_csrng_ctrl = abs_mmio_read32(csrng_ctrl_addr);
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdCsrngRecovAlert));
  abs_mmio_write32(csrng_ctrl_addr, 0);
  CHECK(entropy_complex_check().value == OTCRYPTO_RECOV_ERR.value);
  abs_mmio_write32(csrng_ctrl_addr, old_csrng_ctrl);
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_finish(kTopEarlgreyAlertIdCsrngRecovAlert));

  // Test entropy_complex_check with a disabled EDN0
  uint32_t edn0_ctrl_addr = TOP_EARLGREY_EDN0_BASE_ADDR + EDN_CTRL_REG_OFFSET;
  uint32_t old_edn0_ctrl = abs_mmio_read32(edn0_ctrl_addr);
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_start(kTopEarlgreyAlertIdEdn0RecovAlert));
  abs_mmio_write32(edn0_ctrl_addr, 0);
  CHECK(entropy_complex_check().value == OTCRYPTO_RECOV_ERR.value);
  abs_mmio_write32(edn0_ctrl_addr, old_edn0_ctrl);
  CHECK_STATUS_OK(
      ottf_alerts_expect_alert_finish(kTopEarlgreyAlertIdEdn0RecovAlert));

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, entropy_complex_init_test);
  EXECUTE_TEST(result, entropy_csrng_kat);
  EXECUTE_TEST(result, run_negative_test);
  return status_ok(result);
}
