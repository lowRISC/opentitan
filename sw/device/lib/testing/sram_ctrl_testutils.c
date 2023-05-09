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
                               const sram_ctrl_testutils_data_t data) {
  mmio_region_t region = mmio_region_from_addr(address);
  for (size_t index = 0; index < data.len; ++index) {
    ptrdiff_t offset = (ptrdiff_t)(sizeof(uint32_t)) * (ptrdiff_t)index;
    mmio_region_write32(region, offset, data.words[index]);
  }
}

/**
 * Checks whether the SRAM operation has finished.
 */
static bool check_finished(const dif_sram_ctrl_t *sram_ctrl,
                           dif_sram_ctrl_status_t flag) {
  dif_sram_ctrl_status_bitfield_t status;
  dif_result_t res = dif_sram_ctrl_get_status(sram_ctrl, &status);
  return (res == kDifOk) && (status & flag);
}

status_t sram_ctrl_testutils_scramble(const dif_sram_ctrl_t *sram_ctrl) {
  TRY(dif_sram_ctrl_request_new_key(sram_ctrl));

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
  uint32_t usec = (uint32_t)udiv64_slow(
      1000000, udiv64_slow(kClockFreqCpuHz, 850, NULL) + 1, NULL);

  // Loop until new scrambling key has been obtained.
  LOG_INFO("Waiting for SRAM scrambling to finish");
  IBEX_TRY_SPIN_FOR(check_finished(sram_ctrl, kDifSramCtrlStatusScrKeyValid),
                    usec);
  return OK_STATUS();
}

status_t sram_ctrl_testutils_wipe(const dif_sram_ctrl_t *sram_ctrl) {
  CHECK_DIF_OK(dif_sram_ctrl_wipe(sram_ctrl));
  // The timeout calculation is the same as the scramble timeout.
  uint32_t usec = (uint32_t)udiv64_slow(
      1000000, udiv64_slow(kClockFreqCpuHz, 850, NULL) + 1, NULL);
  LOG_INFO("Waiting for SRAM wipe to finish");
  IBEX_SPIN_FOR(check_finished(sram_ctrl, kDifSramCtrlStatusInitDone), usec);
  return OK_STATUS();
}
