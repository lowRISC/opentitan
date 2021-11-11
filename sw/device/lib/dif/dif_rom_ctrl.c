// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rom_ctrl.h"

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "rom_ctrl_regs.h"  // Generated.

static_assert(ROM_CTRL_DIGEST_DIGEST_FIELD_WIDTH == 32,
              "ROM Controller digest register width changed.");
static_assert(ROM_CTRL_EXP_DIGEST_DIGEST_FIELD_WIDTH == 32,
              "ROM Controller expected digest register width changed.");
static_assert(ROM_CTRL_DIGEST_7_REG_OFFSET == ROM_CTRL_DIGEST_0_REG_OFFSET + 28,
              "ROM Controller digest register layout is not consecutive.");
static_assert(
    ROM_CTRL_EXP_DIGEST_7_REG_OFFSET == ROM_CTRL_EXP_DIGEST_0_REG_OFFSET + 28,
    "ROM Controller expected digest register layout is not consecutive.");

dif_result_t dif_rom_ctrl_get_fatal_alert_cause(
    const dif_rom_ctrl_t *rom_ctrl,
    dif_rom_ctrl_fatal_alert_causes_t *alert_causes) {
  if (rom_ctrl == NULL || alert_causes == NULL) {
    return kDifBadArg;
  }

  *alert_causes = mmio_region_read32(rom_ctrl->base_addr,
                                     ROM_CTRL_FATAL_ALERT_CAUSE_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_rom_ctrl_get_digest(const dif_rom_ctrl_t *rom_ctrl,
                                     dif_rom_ctrl_digest_t *digest) {
  if (rom_ctrl == NULL || digest == NULL) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      rom_ctrl->base_addr, ROM_CTRL_DIGEST_0_REG_OFFSET, digest->digest,
      ROM_CTRL_DIGEST_MULTIREG_COUNT * sizeof(uint32_t));

  return kDifOk;
}

dif_result_t dif_rom_ctrl_get_expected_digest(
    const dif_rom_ctrl_t *rom_ctrl, dif_rom_ctrl_digest_t *expected_digest) {
  if (rom_ctrl == NULL || expected_digest == NULL) {
    return kDifBadArg;
  }

  mmio_region_memcpy_from_mmio32(
      rom_ctrl->base_addr, ROM_CTRL_EXP_DIGEST_0_REG_OFFSET,
      expected_digest->digest,
      ROM_CTRL_EXP_DIGEST_MULTIREG_COUNT * sizeof(uint32_t));

  return kDifOk;
}
