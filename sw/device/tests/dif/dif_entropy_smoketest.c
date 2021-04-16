// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_entropy.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

const test_config_t kTestConfig;

const size_t kEntropyDataNumWords = 12;

const uint32_t kExpectedEntropyData[] = {
    0x65585497, 0xac95d5b1, 0xb2741ebf, 0x055cb180, 0x114d19be, 0x9f27b7f7,
    0x9fbe250d, 0x5ae130f0, 0xf9a679a2, 0x1a4af3e5, 0xa436f52f, 0x613e0635,
};

bool test_main() {
  const dif_entropy_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
  };
  dif_entropy_t entropy;
  CHECK(dif_entropy_init(params, &entropy) == kDifEntropyOk);

  // Disable entropy for test purpose, as it has been turned on by ROM
  CHECK(dif_entropy_disable(&entropy) == kDifEntropyOk);

  const dif_entropy_config_t config = {
      .mode = kDifEntropyModeLfsr,
      .tests =
          {
              [kDifEntropyTestRepCount] = false,
              [kDifEntropyTestAdaptiveProportion] = false,
              [kDifEntropyTestBucket] = false,
              [kDifEntropyTestMarkov] = false,
              [kDifEntropyTestMailbox] = false,
              [kDifEntropyTestVendorSpecific] = false,
          },
      // this field needs to manually toggled by software.  Disable for now
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySingleBitModeDisabled,
      .route_to_firmware = true,
      .sample_rate = 2,
      .lfsr_seed = 2,
  };
  CHECK(dif_entropy_configure(&entropy, config) == kDifEntropyOk);

  uint32_t entropy_data[kEntropyDataNumWords];
  for (uint32_t i = 0; i < kEntropyDataNumWords; ++i) {
    // wait for entropy to become available
    while (dif_entropy_read(&entropy, &entropy_data[i]) != kDifEntropyOk)
      ;
    LOG_INFO("received %x, expectecd %x", entropy_data[i],
             kExpectedEntropyData[i]);
    CHECK(entropy_data[i] == kExpectedEntropyData[i]);
  }

  return true;
}
