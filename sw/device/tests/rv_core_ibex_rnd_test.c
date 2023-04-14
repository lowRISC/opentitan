// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

// Initialize OTTF.
OTTF_DEFINE_TEST_CONFIG();

// Declare two assembly functions defined in `rv_core_ibex_rnd_test.S`.
extern volatile uint32_t rv_core_ibex_rnd_read_and_immediately_check_status();
extern volatile uint32_t
rv_core_ibex_check_rnd_read_possible_while_status_invalid();

enum {
  kRandomDataReads = 32,
  kMaxStatusChecks = 1024,
};

bool test_main(void) {
  // Verify the functionality of the random number generation CSRs.

  // Enable entropy complex, CSRNG and EDN so Ibex can get entropy.
  // Configure entropy in auto_mode to avoid starving the system from entropy,
  // given that boot mode entropy has a limited number of generated bits.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // Initialize Ibex.
  dif_rv_core_ibex_t rv_core_ibex;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR),
      &rv_core_ibex));

  // Perform multiple reads from `RND_DATA` polling `RND_STATUS` in between to
  // only read valid data. Check different random bits are provided each time
  // and that the random data is never zero or all ones.
  uint32_t rnd_data;
  uint32_t previous_rnd_data = 0;
  for (int i = 0; i < kRandomDataReads; i++) {
    CHECK_STATUS_OK(rv_core_ibex_testutils_get_rnd_data(
        &rv_core_ibex, kMaxStatusChecks, &rnd_data));
    CHECK(rnd_data != previous_rnd_data);
    previous_rnd_data = rnd_data;
  }

  // Ensure `RND_STATUS` indicate invalid data immediately after `RND_DATA`
  // read.
  CHECK(rv_core_ibex_rnd_read_and_immediately_check_status() == 0);

  // Perform repeated reads from `RND_DATA` without `RND_STATUS` polling to
  // check read when invalid doesn't block.
  for (int i = 0; i < kRandomDataReads; i++) {
    CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(&rv_core_ibex, &rnd_data));
  }

  // Check to see that we can really do an RND while status is invalid before
  // and after.
  IBEX_SPIN_FOR(rv_core_ibex_testutils_is_rnd_data_valid(&rv_core_ibex),
                kMaxStatusChecks);
  uint32_t status_value =
      rv_core_ibex_check_rnd_read_possible_while_status_invalid();
  CHECK(status_value == 0);

  return true;
}
