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

// Temporary solution to configue/enable the EDN and CSRNG to allow OTBN to run
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

OTBN_DECLARE_APP_SYMBOLS(cfi_test);
OTBN_DECLARE_PTR_SYMBOL(cfi_test, main);
OTBN_DECLARE_PTR_SYMBOL(cfi_test, rv);

static const otbn_app_t kOtbnAppCfiTest = OTBN_APP_T_INIT(cfi_test);
static const otbn_ptr_t kFuncMain = OTBN_PTR_T_INIT(cfi_test, main);
static const otbn_ptr_t kVarRv = OTBN_PTR_T_INIT(cfi_test, rv);

const test_config_t kTestConfig;

bool test_main() {
  setup_edn();

  // Initialize
  otbn_t otbn_ctx;
  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };
  CHECK(otbn_init(&otbn_ctx, otbn_config) == kOtbnOk);
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppCfiTest) == kOtbnOk);

  // Clear OTBN memory
  LOG_INFO("Clearing OTBN memory");
  CHECK(otbn_zero_data_memory(&otbn_ctx) == kOtbnOk);

  CHECK(otbn_call_function(&otbn_ctx, kFuncMain) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(&otbn_ctx) == kOtbnOk);

  // Read back results
  static const uint32_t kRvExp = 7;
  uint32_t rv;
  CHECK(otbn_copy_data_from_otbn(&otbn_ctx, /*len_bytes=*/4, kVarRv, &rv) ==
        kOtbnOk);
  CHECK(rv == kRvExp);

  return true;
}
