// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng_shared.h"

#include "sw/device/lib/base/multibits.h"

#include "csrng_regs.h"  // Generated
#include "edn_regs.h"    // Generated

// The application command header is not specified as a register in the
// hardware specification, so the fields are mapped here by hand. The
// command register also accepts arbitrary 32bit data.
static const bitfield_field32_t kAppCmdFieldFlag0 = {.mask = 0xf, .index = 8};
static const bitfield_field32_t kAppCmdFieldCmdId = {.mask = 0xf, .index = 0};
static const bitfield_field32_t kAppCmdFieldCmdLen = {.mask = 0xf, .index = 4};
static const bitfield_field32_t kAppCmdFieldGlen = {.mask = 0x7ffff,
                                                    .index = 12};

uint32_t csrng_cmd_header_build(
    csrng_app_cmd_id_t id, dif_csrng_entropy_src_toggle_t entropy_src_enable,
    uint32_t cmd_len, uint32_t generate_len) {
  uint32_t reg = bitfield_field32_write(0, kAppCmdFieldCmdId, id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_field32_write(
      reg, kAppCmdFieldFlag0,
      (entropy_src_enable == kDifCsrngEntropySrcToggleDisable
           ? kMultiBitBool4True
           : kMultiBitBool4False));
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, generate_len);
  return reg;
}

dif_result_t csrng_send_app_cmd(mmio_region_t base_addr,
                                csrng_app_cmd_type_t cmd_type,
                                csrng_app_cmd_t cmd) {
  bool ready;
  ptrdiff_t offset;
  uint32_t reg;

  switch (cmd_type) {
    case kCsrngAppCmdTypeCsrng:
      offset = CSRNG_CMD_REQ_REG_OFFSET;
      break;
    case kCsrngAppCmdTypeEdnSw:
      offset = EDN_SW_CMD_REQ_REG_OFFSET;
      break;
    case kCsrngAppCmdTypeEdnGen:
      offset = EDN_GENERATE_CMD_REG_OFFSET;
      break;
    case kCsrngAppCmdTypeEdnRes:
      offset = EDN_RESEED_CMD_REG_OFFSET;
      break;
    default:
      return kDifBadArg;
  }

  // Ensure the `seed_material` array is word-aligned, so it can be loaded to a
  // CPU register with natively aligned loads.
  if (cmd.seed_material != NULL &&
      misalignment32_of((uintptr_t)cmd.seed_material->seed_material) != 0) {
    return kDifBadArg;
  }

  uint32_t cmd_len =
      cmd.seed_material == NULL ? 0 : cmd.seed_material->seed_material_len;
  if (cmd_len & ~kAppCmdFieldCmdLen.mask) {
    return kDifBadArg;
  }

  enum {
    // This is to maintain full compliance with NIST SP 800-90A, which requires
    // the max generate output to be constrained to gen < 2 ^ 12 bits or 0x800
    // 128-bit blocks.
    kMaxGenerateSizeIn128BitBlocks = 0x800,
  };
  if (cmd.generate_len > kMaxGenerateSizeIn128BitBlocks) {
    return kDifOutOfRange;
  }

  if (cmd_type == kCsrngAppCmdTypeEdnSw) {
    // Wait for the status register to be ready to accept the next command.
    do {
      reg = mmio_region_read32(base_addr, EDN_SW_CMD_STS_REG_OFFSET);
      ready = bitfield_bit32_read(reg, EDN_SW_CMD_STS_CMD_RDY_BIT);
    } while (!ready);
  }

  mmio_region_write32(base_addr, offset,
                      csrng_cmd_header_build(cmd.id, cmd.entropy_src_enable,
                                             cmd_len, cmd.generate_len));
  for (size_t i = 0; i < cmd_len; ++i) {
    // If the command is issued to the SW register of the EDN, the reg ready
    // bit needs to be polled before writing each word of additional data.
    if (cmd_type == kCsrngAppCmdTypeEdnSw) {
      do {
        reg = mmio_region_read32(base_addr, EDN_SW_CMD_STS_REG_OFFSET);
        ready = bitfield_bit32_read(reg, EDN_SW_CMD_STS_CMD_REG_RDY_BIT);
      } while (!ready);
    }
    mmio_region_write32(base_addr, offset, cmd.seed_material->seed_material[i]);
  }
  return kDifOk;
}
