// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/sram_ctrl_testutils.h"

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"

/**
 * Main RAM parameters.
 */
static const sram_ctrl_params_t sram_main = {
    .reg_base = TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR,
    .ram_start = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR,
    .ram_end = TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR +
               TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES -
               SRAM_CTRL_DATA_NUM_BYTES,
};

/**
 * Retention RAM parameters.
 */
static const sram_ctrl_params_t sram_ret = {
    .reg_base = TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR,
    .ram_start = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
    .ram_end = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR +
               TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES -
               SRAM_CTRL_DATA_NUM_BYTES,
};

/**
 * Creates SRAM Control handle and initializes the peripheral.
 */
static sram_ctrl_t sram_ctrl_init(const sram_ctrl_params_t *params) {
  sram_ctrl_t sram = {
      .params = params,
  };

  mmio_region_t region = mmio_region_from_addr(params->reg_base);
  CHECK_DIF_OK(dif_sram_ctrl_init(region, &sram.dif));

  return sram;
}

sram_ctrl_t sram_ctrl_main_init(void) { return sram_ctrl_init(&sram_main); }
sram_ctrl_t sram_ctrl_ret_init(void) { return sram_ctrl_init(&sram_ret); }

/**
 * Writes `data` at the `address` in RAM.
 */
static void write_to_ram(uintptr_t address, const sram_ctrl_data_t *data) {
  mmio_region_t region = mmio_region_from_addr(address);
  for (size_t index = 0; index < SRAM_CTRL_DATA_NUM_WORDS; ++index) {
    mmio_region_write32(region, index, data->words[index]);
  }
}

void sram_ctrl_write_to_ram(const sram_ctrl_t *sram,
                            const sram_ctrl_data_t *data) {
  LOG_INFO("Writing data to the start of RAM = %x", sram->params->ram_start);
  write_to_ram(sram->params->ram_start, data);

  LOG_INFO("Writing data to the end of RAM = %x", sram->params->ram_end);
  write_to_ram(sram->params->ram_end, data);
}

/**
 * Reads and compares `data` at the `address` in RAM.
 *
 * The read data is word by word compared against the expected data.
 * Caller can request to check for equality or inequality.
 */
static bool read_from_ram_check(uintptr_t address,
                                const sram_ctrl_data_t *expected, bool eq) {
  mmio_region_t region = mmio_region_from_addr(address);
  for (size_t index = 0; index < SRAM_CTRL_DATA_NUM_WORDS; ++index) {
    // The read data is tested for equality against the expected data, and
    // then the result is checked against the requested equality condition.
    uint32_t read_word = mmio_region_read32(region, index);
    if ((read_word == expected->words[index]) != eq) {
      if (eq) {
        LOG_INFO("Equality check failure:");
      } else {
        LOG_INFO("Inequality check failure:");
      }

      LOG_INFO("READ_WORD[%x], CONTROL_WORD[%x], INDEX = %d", read_word,
               expected->words[index], index);

      return false;
    }
  }

  return true;
}

bool sram_ctrl_read_from_ram_eq(const sram_ctrl_t *sram,
                                const sram_ctrl_data_t *expected) {
  LOG_INFO("Reading from the start of RAM = %x", sram->params->ram_start);
  if (!read_from_ram_check(sram->params->ram_start, expected, true)) {
    return false;
  }

  LOG_INFO("Reading from the end of RAM = %x", sram->params->ram_end);
  if (!read_from_ram_check(sram->params->ram_end, expected, true)) {
    return false;
  }

  return true;
}

bool sram_ctrl_read_from_ram_neq(const sram_ctrl_t *sram,
                                 const sram_ctrl_data_t *expected) {
  LOG_INFO("Reading from the start of RAM = %x", sram->params->ram_start);
  if (!read_from_ram_check(sram->params->ram_start, expected, false)) {
    return false;
  }

  LOG_INFO("Reading from the end of RAM = %x", sram->params->ram_end);
  if (!read_from_ram_check(sram->params->ram_end, expected, false)) {
    return false;
  }

  return true;
}

// Checks whether the SRAM scramble operation has finished.
static bool scramble_finished(const sram_ctrl_t *sram) {
  dif_sram_ctrl_status_bitfield_t status;
  CHECK_DIF_OK(dif_sram_ctrl_get_status(&sram->dif, &status));
  return status & kDifSramCtrlStatusScrKeyValid;
}

void sram_ctrl_scramble(const sram_ctrl_t *sram) {
  CHECK_DIF_OK(dif_sram_ctrl_request_new_key(&sram->dif));

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
  uint32_t usec = 1000000 / (kClockFreqCpuHz / 850) + 1;

  // Loop until new scrambling key has been obtained.
  LOG_INFO("Waiting for SRAM scrambling to finish");
  IBEX_SPIN_FOR(scramble_finished(sram), usec);
}
