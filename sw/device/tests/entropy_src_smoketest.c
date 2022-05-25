// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

const size_t kEntropyDataNumWords = 12;

// This expected value seems to require frequent updating.  If it turns
// out that changes to the overall system start causing race conditions
// we may want to relax the requirement for exact binary equivalence.
//
// Issue #10092 has been opened to discuss this.

const uint32_t kExpectedEntropyData[] = {
    0x38a9e15d, 0xc615d072, 0x15f21dc9, 0x38f06e56, 0x790a2a87, 0x8bff3d11,
    0xd56913da, 0x75dc72c3, 0xee2d38a2, 0xabfddaec, 0x3837e88b, 0x29cf1c12};

bool test_main() {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));

  // Disable entropy for test purpose, as it has been turned on by ROM
  CHECK_DIF_OK(dif_entropy_src_disable(&entropy_src));

  const dif_entropy_src_config_t config = {
      .mode = kDifEntropySrcModePtrng,
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
      .route_to_firmware = true,
      .fw_override = {
          .enable = false,
          .entropy_insert_enable = false,
          .buffer_threshold = kDifEntropyFifoIntDefaultThreshold,
      }};
  CHECK_DIF_OK(dif_entropy_src_configure(&entropy_src, config));

  uint32_t entropy_data[kEntropyDataNumWords];
  uint32_t result = 0;
  for (uint32_t i = 0; i < kEntropyDataNumWords; ++i) {
    // wait for entropy to become available
    while (dif_entropy_src_read(&entropy_src, &entropy_data[i]) != kDifOk)
      ;
    LOG_INFO("received 0x%x, expected 0x%x", entropy_data[i],
             kExpectedEntropyData[i]);
    result |= entropy_data[i] ^ kExpectedEntropyData[i];
  }

  return result == 0;
}
