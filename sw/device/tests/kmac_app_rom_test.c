// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "devicetables.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rom_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_rom_ctrl_digest_t computed_digest;
  dif_rom_ctrl_digest_t expected_digest;
  dif_rom_ctrl_t rom_ctrl;

  for (size_t rom_idx = 0; rom_idx < kDtRomCtrlCount; rom_idx++) {
    LOG_INFO("Checking rom_ctrl%d...", rom_idx);
    // initialize rom_ctrl
    CHECK_DIF_OK(dif_rom_ctrl_init_from_dt(&kDtRomCtrl[rom_idx], &rom_ctrl));

    // get computed and expected digests and check that they match
    CHECK_DIF_OK(dif_rom_ctrl_get_digest(&rom_ctrl, &computed_digest));
    CHECK_DIF_OK(dif_rom_ctrl_get_expected_digest(&rom_ctrl, &expected_digest));
    CHECK_ARRAYS_EQ(
        computed_digest.digest, expected_digest.digest,
        ROM_CTRL_DIGEST_MULTIREG_COUNT,
        "Mismatch between computed and expected digest for rom_ctrl%d.",
        rom_idx);
  }

  return true;
}
