// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

status_t test_ctr_drbg_ctr0(const dif_csrng_t *csrng) {
  TRY(csrng_testutils_cmd_ready_wait(csrng));
  TRY(dif_csrng_uninstantiate(csrng));
  TRY(csrng_testutils_fips_instantiate_kat(csrng, /*fail_expected=*/false));
  TRY(csrng_testutils_fips_generate_kat(csrng));
  return OK_STATUS();
}

bool test_main(void) {
  dif_csrng_t csrng;
  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  CHECK_STATUS_OK(test_ctr_drbg_ctr0(&csrng));

  return true;
}
