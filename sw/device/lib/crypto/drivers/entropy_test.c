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

static void entropy_complex_init_test(void) {
  CHECK_STATUS_OK(entropy_complex_init());

  // The following test requests entropy from both EDN0 and EDN1.
  dif_otbn_t otbn;
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));
  otbn_randomness_test_start(&otbn);
  CHECK(otbn_randomness_test_end(&otbn, /*skip_otbn_don_check=*/false));
}

bool test_main(void) {
  status_t result = entropy_csrng_kat();
  if (!status_ok(result)) {
    LOG_ERROR("entropy_csrng_kat: %r\n", result);
    return false;
  }
  entropy_complex_init_test();
  return true;
}
