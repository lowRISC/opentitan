// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/crypto/drivers/entropy.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy_kat.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/otbn_randomness_impl.h"

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
  otbn_randomness_test_start(&otbn);
  TRY_CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_don_check=*/false));
  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, entropy_complex_init_test);
  EXECUTE_TEST(result, entropy_csrng_kat);
  return status_ok(result);
}
