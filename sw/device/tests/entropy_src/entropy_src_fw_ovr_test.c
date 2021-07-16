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
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode. */
  kEntropyFifoBufferSize = 32,
};

/**
 * Flushes the data entropy buffer until there is no data available to read.
 *
 * Asserts test error if any of the returned words is equal to zero. Logs the
 * number of entropy words flushed in a single call.
 *
 * @param entropy An entropy source instance.
 */
static void entropy_data_flush(dif_entropy_t *entropy) {
  uint32_t entropy_bits;
  uint32_t read_count = 0;
  while (dif_entropy_avail(entropy) == kDifEntropyOk) {
    CHECK(dif_entropy_read(entropy, &entropy_bits) == kDifEntropyOk);
    CHECK(entropy_bits != 0);
    read_count++;
  }
  LOG_INFO("Flushed %d entropy words.", read_count);
}

/**
 * Configures the entropy source module in firmware override mode.
 *
 * Output is routed to firmware, and the fw_override mode is enabled to get data
 * post-health tests and before the pre conditioner block.
 *
 * @param entropy An entropy source instance.
 */
static void entropy_with_fw_override_enable(dif_entropy_t *entropy) {
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
      .fw_override =
          {
              .enable = true,
              .entropy_insert_enable = true,
              .buffer_threshold = kEntropyFifoBufferSize,
          },
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
  CHECK(dif_entropy_disable(entropy) == kDifEntropyOk);
  entropy_with_fw_override_enable(entropy);
  entropy_data_flush(entropy);

  // Read data from the obeservation and write it back into the pre conditioner
  // until there is data available in the output buffer.
  uint32_t buf[kEntropyFifoBufferSize] = {0};
  uint32_t word_count = 0;
  do {
    CHECK(dif_entropy_fifo_read(entropy, buf, kEntropyFifoBufferSize) ==
          kDifEntropyOk);
    for (size_t i = 0; i < kEntropyFifoBufferSize; ++i) {
      CHECK(buf[i] != 0);
    }
    CHECK(dif_entropy_fifo_write(entropy, buf, kEntropyFifoBufferSize) ==
          kDifEntropyOk);
    word_count += kEntropyFifoBufferSize;
  } while (dif_entropy_avail(entropy) == kDifEntropyDataUnAvailable);
  LOG_INFO("Processed %d words via FIFO_OVR buffer.", word_count);
  entropy_data_flush(entropy);
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
