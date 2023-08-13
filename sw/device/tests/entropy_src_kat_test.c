// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/entropy_src_kat_impl.h"
#include "sw/ip/entropy_src/dif/dif_entropy_src.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR),
      &entropy_src));
  entropy_src_kat_test(&entropy_src);
  return true;
}
