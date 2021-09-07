// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/testing/check.h"

#include "edn_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static void setup_entropy_src(void) {
  const dif_entropy_src_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
  };
  dif_entropy_src_t entropy;
  CHECK(dif_entropy_src_init(params, &entropy) == kDifEntropySrcOk);

  // Disable entropy for test purpose, as it has been turned on by ROM
  CHECK(dif_entropy_src_disable(&entropy) == kDifEntropySrcOk);

  const dif_entropy_src_config_t config = {
      .mode = kDifEntropySrcModeLfsr,
      .tests =
          {
              [kDifEntropySrcTestRepCount] = false,
              [kDifEntropySrcTestAdaptiveProportion] = false,
              [kDifEntropySrcTestBucket] = false,
              [kDifEntropySrcTestMarkov] = false,
              [kDifEntropySrcTestMailbox] = false,
              [kDifEntropySrcTestVendorSpecific] = false,
          },
      // this field needs to manually toggled by software.  Disable for now
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .route_to_firmware = false,
      .sample_rate = 2,
      .lfsr_seed = 0,
  };
  CHECK(dif_entropy_src_configure(&entropy, config) == kDifEntropySrcOk);
}

static void setup_csrng(void) {
  const dif_csrng_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR),
  };
  dif_csrng_t csrng;
  CHECK(dif_csrng_init(params, &csrng) == kDifCsrngOk);
  CHECK(dif_csrng_configure(&csrng) == kDifCsrngOk);
}

static void setup_edn(void) {
  // Temporary solution to configure/enable the EDN and CSRNG to allow OTBN to
  // run before a DIF is available,
  // https://github.com/lowRISC/opentitan/issues/6082
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x55aa);
  mmio_region_write32(mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR),
                      EDN_CTRL_REG_OFFSET, 0x55aa);
}

void entropy_testutils_boot_mode_init(void) {
  setup_entropy_src();
  setup_csrng();
  setup_edn();
}
