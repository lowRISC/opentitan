// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

enum {
  kBase = TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR,
};

OTTF_DEFINE_TEST_CONFIG();

static status_t ibex_entropy_test(void) {
  LOG_INFO("Running IBEX entropy test.");

  // Read the initial value of the RND_DATA CSR.
  uint32_t rnd_data0 = ibex_rnd32_read();
  // Read RND_DATA again and check if it changed.
  uint32_t rnd_data1 = ibex_rnd32_read();
  TRY_CHECK(rnd_data0 != rnd_data1);

  return OK_STATUS();
}

static status_t ibex_security_config_test(void) {
  LOG_INFO("Running IBEX security config test.");

  uint32_t original_csr;
  CSR_READ(CSR_REG_CPUCTRL, &original_csr);
  CSR_SET_BITS(CSR_REG_CPUCTRL, 0x6);
  uint32_t current_csr;
  CSR_READ(CSR_REG_CPUCTRL, &current_csr);

  if (((current_csr >> 1) & 0x3) == 0x3) {
    // Check the positive path
    TRY_CHECK(ibex_check_security_config() == kHardenedBoolTrue);

    // Check the negative path
    CSR_CLEAR_BITS(CSR_REG_CPUCTRL, 0x2);
    TRY_CHECK(ibex_check_security_config() == kHardenedBoolFalse);
  } else {
    // Only check the negative path
    TRY_CHECK(ibex_check_security_config() == kHardenedBoolFalse);
  }

  if (original_csr & 0x2) {
    CSR_SET_BITS(CSR_REG_CPUCTRL, 0x2);
  } else {
    CSR_CLEAR_BITS(CSR_REG_CPUCTRL, 0x2);
  }

  if (original_csr & 0x4) {
    CSR_SET_BITS(CSR_REG_CPUCTRL, 0x4);
  } else {
    CSR_CLEAR_BITS(CSR_REG_CPUCTRL, 0x4);
  }

  return OK_STATUS();
}

static status_t ibex_icache_test(void) {
  LOG_INFO("Running IBEX iCache disable/restore test.");

  hardened_bool_t icache_state_1;
  hardened_bool_t icache_state_2;

  // Test ibex_disable_icache where the icache was enabled
  CSR_SET_BITS(CSR_REG_CPUCTRL, 1);
  TRY(ibex_disable_icache(&icache_state_1));
  TRY_CHECK(icache_state_1 == kHardenedBoolTrue);

  // Test ibex_disable_icache where the icache was disabled
  TRY(ibex_disable_icache(&icache_state_2));
  TRY_CHECK(icache_state_2 == kHardenedBoolFalse);

  // Test the restore
  ibex_restore_icache(icache_state_2);
  uint32_t csr;
  CSR_READ(CSR_REG_CPUCTRL, &csr);
  TRY_CHECK((csr & 1) == 0);
  ibex_restore_icache(icache_state_1);
  CSR_READ(CSR_REG_CPUCTRL, &csr);
  TRY_CHECK((csr & 1) == 1);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, ibex_entropy_test);
  EXECUTE_TEST(result, ibex_security_config_test);
  EXECUTE_TEST(result, ibex_icache_test);

  return status_ok(result);
}
