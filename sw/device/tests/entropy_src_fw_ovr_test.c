// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * The size of the buffer used in firmware to process the entropy bits in
   * firmware override mode.
   */
  kEntropyFifoBufferSize = 16,
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

  while (dif_entropy_src_is_entropy_available(entropy_src) == kDifOk) {
    CHECK_DIF_OK(dif_entropy_src_non_blocking_read(entropy_src, &entropy_bits));
    CHECK(entropy_bits != 0);
    read_count++;
    if (read_count >= kMaxReadCount) {
      break;
    }
  }
  LOG_INFO("Flushed %d entropy words.", read_count);
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
  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_STATUS_OK(
      entropy_testutils_fw_override_enable(entropy, kEntropyFifoBufferSize,
                                           /*route_to_firmware=*/true,
                                           /*bypass_conditioner=*/false));
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
    // Start the SHA3 process so that it is ready to accept entropy data.
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        entropy, kDifToggleEnabled));
    CHECK_DIF_OK(dif_entropy_src_fw_ov_data_write(
        entropy, buf, kEntropyFifoBufferSize, NULL));
    word_count += kEntropyFifoBufferSize;
    // Stop insertion so that the SHA3 can process data.
    CHECK_DIF_OK(dif_entropy_src_fw_override_sha3_start_insert(
        entropy, kDifToggleDisabled));
  } while (dif_entropy_src_is_entropy_available(entropy) == kDifUnavailable);
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
