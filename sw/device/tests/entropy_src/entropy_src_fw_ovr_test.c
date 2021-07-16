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

enum {
  kEntropyFIFOBufferSize = 64,
  kEntropyDataNumWords = 12,
};

static void toggle_entropy_enable(dif_entropy_t *entropy) {
  CHECK(dif_entropy_disable(entropy) == kDifEntropyOk);

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
      .reset_health_test_registers = false,
      .single_bit_mode = kDifEntropySingleBitModeDisabled,
      .route_to_firmware = true,
      .sample_rate = 2,
      .lfsr_seed = 2,
  };
  CHECK(dif_entropy_configure(entropy, config) == kDifEntropyOk);
}

/**
 * Test the firmware override path.
 *
 * This tests disconnects the observation buffer from the entropy src
 * pre-conditioner block to read the raw entropy data after the hardware
 * health tests. It then feeds the data back into the conditioner block until
 * there is data available in the output FIFO.
 *
 * @param entropy An Entropy handle.
 */
void test_firmware_override(dif_entropy_t *entropy) {
  // Disconnect the observe buffer and toggle entropy enable to restart the
  // entropy source with the path to the pre-conditioner block open.
  CHECK(dif_entropy_fifo_disconnect(entropy) == kDifEntropyOk);
  toggle_entropy_enable(entropy);

  uint32_t buf[kEntropyFIFOBufferSize] = {0};
  CHECK(dif_entropy_fifo_read(entropy, buf, ARRAYSIZE(buf)) ==
   kDifEntropyOk);

  for (size_t i = 0; i < ARRAYSIZE(buf); ++i) {
    CHECK(buf[i] != 0);
  }
  CHECK(dif_entropy_fifo_write(entropy, buf, ARRAYSIZE(buf)) == kDifEntropyOk);
  CHECK(dif_entropy_avail(entropy) == kDifEntropyDataUnAvailable);
  CHECK(dif_entropy_fifo_reconnect(entropy));
}

bool test_main() {
  const dif_entropy_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR),
  };
  dif_entropy_t entropy;
  CHECK(dif_entropy_init(params, &entropy) == kDifEntropyOk);

  test_firmware_override(&entropy);
  return true;
}
