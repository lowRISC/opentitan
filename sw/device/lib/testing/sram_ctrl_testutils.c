// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/sram_ctrl_testutils.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

void sram_ctrl_testutils_write(uintptr_t address,
                               const sram_ctrl_testutils_data_t *data) {
  mmio_region_t region = mmio_region_from_addr(address);
  for (size_t index = 0; index < SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS; ++index) {
    mmio_region_write32(region, sizeof(uint32_t) * index, data->words[index]);
  }
}

/**
 * Reads data from `address` in SRAM and compares against `expected`.
 *
 * The read data is word by word compared against the expected data.
 * Caller can request to check for equality or inequality through `eq`.
 */
static bool read_from_ram_check(uintptr_t address,
                                const sram_ctrl_testutils_data_t *expected,
                                bool eq) {
  mmio_region_t region = mmio_region_from_addr(address);
  for (size_t index = 0; index < SRAM_CTRL_TESTUTILS_DATA_NUM_WORDS; ++index) {
    uint32_t read_word = mmio_region_read32(region, sizeof(uint32_t) * index);
    if ((read_word == expected->words[index]) != eq) {
      LOG_INFO("READ_WORD[%x], CONTROL_WORD[%x], INDEX = %d", read_word,
               expected->words[index], index);

      return false;
    }
  }

  return true;
}

bool sram_ctrl_testutils_read_check_eq(
    uintptr_t address, const sram_ctrl_testutils_data_t *expected) {
  if (!read_from_ram_check(address, expected, true)) {
    LOG_INFO("Equality check failure");
    return false;
  }

  return true;
}

bool sram_ctrl_testutils_read_check_neq(
    uintptr_t address, const sram_ctrl_testutils_data_t *expected) {
  if (!read_from_ram_check(address, expected, false)) {
    LOG_INFO("Inequality check failure");
    return false;
  }

  return true;
}

/**
 * Checks whether the SRAM scramble operation has finished.
 */
static bool scramble_finished(const dif_sram_ctrl_t *sram_ctrl) {
  dif_sram_ctrl_status_bitfield_t status;
  CHECK_DIF_OK(dif_sram_ctrl_get_status(sram_ctrl, &status));
  return status & kDifSramCtrlStatusScrKeyValid;
}

void sram_ctrl_testutils_scramble(const dif_sram_ctrl_t *sram_ctrl) {
  CHECK_DIF_OK(dif_sram_ctrl_request_new_key(sram_ctrl));

  // Calculate the timeout time.
  // The SRAM Controller documentation says that it takes approximately 800
  // cycles to perform the SRAM scrambling operation (50 cycles were added to
  // this number to be on a safe side).
  //
  // The calculation is equivalent of (1us / clk) * 850 (clock period expressed
  // in micro seconds multiplied by number of cycles needed to perform
  // the RAM scrambling operation).
  //
  // Expressing this calculation in 1us / (clk / 850) is less intuitive, but
  // makes more sense when dealing with the integer division, as when the clock
  // frequency is greater than 1 million hertz, the first expression will give
  // inaccurate results due to clock period being zero. It should not be a
  // problem with the second version, as clock frequency won't be less than
  // 850. We add 1 microsecond to account for flooring.
  uint32_t usec =
      udiv64_slow(1000000, udiv64_slow(kClockFreqCpuHz, 850, NULL) + 1, NULL);

  // Loop until new scrambling key has been obtained.
  LOG_INFO("Waiting for SRAM scrambling to finish");
  IBEX_SPIN_FOR(scramble_finished(sram_ctrl), usec);
}

/**
 * Checks whether the SRAM wipe operation has finished.
 */
static bool wipe_finished(const dif_sram_ctrl_t *sram_ctrl) {
  dif_sram_ctrl_status_bitfield_t status;
  CHECK_DIF_OK(dif_sram_ctrl_get_status(sram_ctrl, &status));
  return status & kDifSramCtrlStatusInitDone;
}

void sram_ctrl_testutils_wipe(const dif_sram_ctrl_t *sram_ctrl) {
  CHECK_DIF_OK(dif_sram_ctrl_wipe(sram_ctrl));
  // The timeout calculation is the same as the scramble timeout.
  uint32_t usec =
      udiv64_slow(1000000, udiv64_slow(kClockFreqCpuHz, 850, NULL) + 1, NULL);
  LOG_INFO("Waiting for SRAM wipe to finish");
  IBEX_SPIN_FOR(wipe_finished(sram_ctrl), usec);
}

void sram_ctrl_testutils_check_backdoor_write(uintptr_t backdoor_addr,
                                              uint32_t num_words,
                                              uint32_t offset_addr,
                                              const uint8_t *expected_bytes) {
  mmio_region_t mem_region = mmio_region_from_addr(backdoor_addr);
  uint32_t backdoor_data[num_words];
  uint32_t expected_data[num_words];

  for (int i = 0; i < num_words; ++i) {
    backdoor_data[i] =
        mmio_region_read32(mem_region, sizeof(uint32_t) * (offset_addr + i));
    // The expected data bytes are organized little-endian.
    expected_data[i] = expected_bytes[(i * sizeof(uint32_t)) + 3] << 24 |
                       expected_bytes[(i * sizeof(uint32_t)) + 2] << 16 |
                       expected_bytes[(i * sizeof(uint32_t)) + 1] << 8 |
                       expected_bytes[(i * sizeof(uint32_t))];
    CHECK(backdoor_data[i] == expected_data[i]);
  }
}
