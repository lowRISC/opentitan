// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

const test_config_t kTestConfig;

bool test_main() {
  const dif_csrng_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
  };
  dif_csrng_t csrng;
  CHECK(dif_csrng_init(params, &csrng) == kDifCsrngOk);

  const dif_csrng_config_t config = {
      .debug_config = {.bypass_aes_cipher = false},
  };
  CHECK(dif_csrng_configure(&csrng, config) == kDifCsrngOk);

  // TODO: Instantiate
  // TODO: Generate
  // TODO: Check for output ready
  // TODO: Compare output

  return true;
}
