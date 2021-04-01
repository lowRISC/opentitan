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

// TODO: These values are specific to verilator right now and will not work
// for DV or FPGA, see #5941
const uint32_t kExpectedEntropyData[] = {
    0x0a3f4df0, 0x4e36fad2, 0xb5f3e0b9, 0x918f5ec0, 0x54ddd680, 0x62f04975,
    0x700cf2f2, 0x61044bfe, 0x723d6c89, 0xe2d70e19, 0x5f02a234, 0xbf586fcc,

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
    // LOG_INFO("received %x, expectecd %x", entropy_data[i],
    // kExpectedEntropyData[i]);
    CHECK(entropy_data[i] == kExpectedEntropyData[i]);
  }

  return true;
}
