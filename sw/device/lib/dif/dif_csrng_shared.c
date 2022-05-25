// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng_shared.h"

OT_WARN_UNUSED_RESULT
dif_result_t csrng_send_app_cmd(mmio_region_t base_addr, ptrdiff_t offset,
                                csrng_app_cmd_t cmd) {
  // The application command header is not specified as a register in the
  // hardware specification, so the fields are mapped here by hand. The
  // command register also accepts arbitrary 32bit data.
  static const uint32_t kAppCmdBitFlag0 = 8;
  static const bitfield_field32_t kAppCmdFieldCmdId = {.mask = 0xf, .index = 0};
  static const bitfield_field32_t kAppCmdFieldCmdLen = {.mask = 0xf,
                                                        .index = 4};
  static const bitfield_field32_t kAppCmdFieldGlen = {.mask = 0x7ffff,
                                                      .index = 12};

  uint32_t cmd_len =
      cmd.seed_material == NULL ? 0 : cmd.seed_material->seed_material_len;

  if (cmd_len & ~kAppCmdFieldCmdLen.mask) {
    return kDifBadArg;
  }

  // Build and write application command header.
  uint32_t reg = bitfield_field32_write(0, kAppCmdFieldCmdId, cmd.id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_bit32_write(reg, kAppCmdBitFlag0, cmd.entropy_src_enable);
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, cmd.generate_len);
  mmio_region_write32(base_addr, offset, reg);

  for (size_t i = 0; i < cmd_len; ++i) {
    mmio_region_write32(base_addr, offset, cmd.seed_material->seed_material[i]);
  }
  return kDifOk;
}
