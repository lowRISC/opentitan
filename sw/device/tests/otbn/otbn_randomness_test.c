// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Temporary solution to configure/enable the EDN and CSRNG to allow OTBN to run
// before a DIF is available, https://github.com/lowRISC/opentitan/issues/6082
static const uint32_t kEntropySrcConfRegOffset = 0x18;
static const uint32_t kCsrngCtrlRegOffset = 0x14;
static const uint32_t kEdnCtrlRegOffset = 0x14;

static void setup_edn(void) {
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
                      kEntropySrcConfRegOffset, 0x2);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
                      kCsrngCtrlRegOffset, 0x1);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      kEdnCtrlRegOffset, 0x9);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR),
                      kEdnCtrlRegOffset, 0x9);
}

OTBN_DECLARE_APP_SYMBOLS(randomness);
OTBN_DECLARE_PTR_SYMBOL(randomness, main);
OTBN_DECLARE_PTR_SYMBOL(randomness, rv);
OTBN_DECLARE_PTR_SYMBOL(randomness, fail_idx);
OTBN_DECLARE_PTR_SYMBOL(randomness, rnd_out);
OTBN_DECLARE_PTR_SYMBOL(randomness, urnd_out);

static const otbn_app_t kOtbnAppCfiTest = OTBN_APP_T_INIT(randomness);
static const otbn_ptr_t kFuncMain = OTBN_PTR_T_INIT(randomness, main);
static const otbn_ptr_t kVarRv = OTBN_PTR_T_INIT(randomness, rv);
static const otbn_ptr_t kVarFailIdx = OTBN_PTR_T_INIT(randomness, fail_idx);
static const otbn_ptr_t kVarRndOut = OTBN_PTR_T_INIT(randomness, rnd_out);
static const otbn_ptr_t kVarUrndOut = OTBN_PTR_T_INIT(randomness, urnd_out);

const test_config_t kTestConfig;

/**
 * LOG_INFO with a 256b unsigned integer as hexadecimal number with a prefix.
 */
static void print_uint256(otbn_t *ctx, const otbn_ptr_t var,
                          const char *prefix) {
  uint32_t data[32 / sizeof(uint32_t)];
  CHECK(otbn_copy_data_from_otbn(ctx, /*len_bytes=*/32, var, &data) == kOtbnOk);
  LOG_INFO("%s0x%08x%08x%08x%08x%08x%08x%08x%08x", prefix, data[7], data[6],
           data[5], data[4], data[3], data[2], data[1], data[0]);
}

bool test_main() {
  setup_edn();

  // Initialize
  otbn_t otbn_ctx;
  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };
  CHECK(otbn_init(&otbn_ctx, otbn_config) == kOtbnOk);
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppCfiTest) == kOtbnOk);

  CHECK(otbn_call_function(&otbn_ctx, kFuncMain) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(&otbn_ctx) == kOtbnOk);

  // Check for successful test execution (self-reported).
  uint32_t rv;
  CHECK(otbn_copy_data_from_otbn(&otbn_ctx, /*len_bytes=*/4, kVarRv, &rv) ==
        kOtbnOk);

  // Log some of the random numbers we got (for manual checks).
  print_uint256(&otbn_ctx, kVarRndOut, "rnd = ");
  print_uint256(&otbn_ctx, kVarUrndOut, "urnd = ");

  if (rv != 0) {
    uint32_t fail_idx;
    CHECK(otbn_copy_data_from_otbn(&otbn_ctx, /*len_bytes=*/4, kVarFailIdx,
                                   &fail_idx) == kOtbnOk);
    LOG_INFO("ERROR: Test with index %d failed.", fail_idx);
    return false;
  }

  return true;
}
