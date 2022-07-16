// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
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
static void entropy_data_flush(dif_entropy_src_t *entropy_src) {
  uint32_t entropy_bits;
  uint32_t read_count = 0;

  // TODO: Remove this limit. Entropy source should block if there is no entropy
  // available in FW override mode.
  const uint32_t kMaxReadCount = 12;

  while (dif_entropy_src_avail(entropy_src) == kDifOk) {
    CHECK_DIF_OK(dif_entropy_src_read(entropy_src, &entropy_bits));
    CHECK(entropy_bits != 0);
    read_count++;
    if (read_count >= kMaxReadCount) {
      break;
    }
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
static void entropy_with_fw_override_enable(dif_entropy_src_t *entropy_src) {
  const dif_entropy_src_fw_override_config_t fw_override_config = {
      .entropy_insert_enable = true,
      .buffer_threshold = kEntropyFifoBufferSize,
  };
  CHECK_DIF_OK(dif_entropy_src_fw_override_configure(
      entropy_src, fw_override_config, kDifToggleEnabled));
  const dif_entropy_src_config_t config = {
      .fips_enable = true,
      .route_to_firmware = true,
      .single_bit_mode = kDifEntropySrcSingleBitModeDisabled,
      .health_test_threshold_scope = false, /*default*/
      .health_test_window_size = 0x0200,    /*default*/
      .alert_threshold = 2,                 /*default*/
  };
  CHECK_DIF_OK(
      dif_entropy_src_configure(entropy_src, config, kDifToggleEnabled));
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
void test_firmware_override(dif_entropy_src_t *entropy) {
  CHECK_DIF_OK(dif_entropy_src_set_enabled(entropy, kDifToggleDisabled));
  entropy_with_fw_override_enable(entropy);
  entropy_data_flush(entropy);

  // Read data from the observation FIFO and write it back into the
  // pre-conditioner until there is data available in the output buffer.
  uint32_t buf[kEntropyFifoBufferSize] = {0};
  uint32_t word_count = 0;
  do {
    CHECK_DIF_OK(dif_entropy_src_observe_fifo_blocking_read(
        entropy, buf, kEntropyFifoBufferSize));
    for (size_t i = 0; i < kEntropyFifoBufferSize; ++i) {
      CHECK(buf[i] != 0);
    }
    CHECK_DIF_OK(dif_entropy_src_observe_fifo_write(entropy, buf,
                                                    kEntropyFifoBufferSize));
    word_count += kEntropyFifoBufferSize;
  } while (dif_entropy_src_avail(entropy) == kDifUnavailable);
  LOG_INFO("Processed %d words via FIFO_OVR buffer.", word_count);
  entropy_data_flush(entropy);
}

bool test_main(void) {
  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init(
      mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR), &entropy_src));
  test_firmware_override(&entropy_src);
  return true;
}
