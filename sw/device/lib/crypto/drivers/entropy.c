// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"

#include "csrng_regs.h"  // Generated
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  kBaseCsrng = TOP_EARLGREY_CSRNG_BASE_ADDR,

  /**
   * CSRNG genbits buffer size in uint32_t words.
   */
  kEntropyCsrngBitsBufferNumWords = 4,
};

/**
 * Supported CSRNG application commands.
 * See https://docs.opentitan.org/hw/ip/csrng/doc/#command-header for
 * details.
 */
// TODO(#14542): Harden csrng/edn command fields.
typedef enum entropy_csrng_op {
  kEntropyDrbgOpInstantiate = 1,
  kEntropyDrbgOpReseed = 2,
  kEntropyDrbgOpGenerate = 3,
  kEntropyDrbgOpUpdate = 4,
  kEntropyDrbgOpUnisntantiate = 5,
} entropy_csrng_op_t;

/**
 * CSRNG application interface command header parameters.
 */
typedef struct entropy_csrng_cmd {
  /**
   * Application command ID.
   */
  entropy_csrng_op_t id;
  /**
   * Entropy source enable.
   *
   * Mapped to flag0 in the hardware command interface.
   */
  hardened_bool_t disable_trng_input;
  const entropy_seed_material_t *seed_material;
  /**
   * Generate length. Specified as number of 128bit blocks.
   */
  uint32_t generate_len;
} entropy_csrng_cmd_t;

#define ENTROPY_CMD(m, i) ((bitfield_field32_t){.mask = m, .index = i})

OT_WARN_UNUSED_RESULT
static status_t csrng_send_app_cmd(uint32_t reg_address,
                                   entropy_csrng_cmd_t cmd) {
  uint32_t reg;
  bool cmd_ready;
  bool cmd_error;
  do {
    reg = abs_mmio_read32(kBaseCsrng + CSRNG_SW_CMD_STS_REG_OFFSET);
    cmd_ready = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT);
  } while (!cmd_ready);

  // The application command header is not specified as a register in the
  // hardware specification, so the fields are mapped here by hand. The
  // command register also accepts arbitrary 32bit data.
  static const bitfield_field32_t kAppCmdFieldFlag0 = ENTROPY_CMD(0xf, 8);
  static const bitfield_field32_t kAppCmdFieldCmdId = ENTROPY_CMD(0xf, 0);
  static const bitfield_field32_t kAppCmdFieldCmdLen = ENTROPY_CMD(0xf, 4);
  static const bitfield_field32_t kAppCmdFieldGlen = ENTROPY_CMD(0x7ffff, 12);

  uint32_t cmd_len = cmd.seed_material == NULL ? 0 : cmd.seed_material->len;

  if (cmd_len & ~kAppCmdFieldCmdLen.mask) {
    return INTERNAL();
  }

  // TODO: Consider removing this since the driver will be constructing these
  // commands internally.
  // Ensure the `seed_material` array is word-aligned, so it can be loaded to a
  // CPU register with natively aligned loads.
  if (cmd.seed_material != NULL &&
      misalignment32_of((uintptr_t)cmd.seed_material->data) != 0) {
    return INTERNAL();
  }

  // Build and write application command header.
  reg = bitfield_field32_write(0, kAppCmdFieldCmdId, cmd.id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, cmd.generate_len);

  if (launder32(cmd.disable_trng_input) == kHardenedBoolTrue) {
    reg = bitfield_field32_write(reg, kAppCmdFieldFlag0, kMultiBitBool4True);
  }

  abs_mmio_write32(reg_address, reg);

  for (size_t i = 0; i < cmd_len; ++i) {
    abs_mmio_write32(reg_address, cmd.seed_material->data[i]);
  }
  return OK_STATUS();
}

status_t entropy_csrng_instantiate(
    hardened_bool_t disable_trng_input,
    const entropy_seed_material_t *seed_material) {
  return csrng_send_app_cmd(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET,
                            (entropy_csrng_cmd_t){
                                .id = kEntropyDrbgOpInstantiate,
                                .disable_trng_input = disable_trng_input,
                                .seed_material = seed_material,
                                .generate_len = 0,
                            });
}

status_t entropy_csrng_reseed(hardened_bool_t disable_trng_input,
                              const entropy_seed_material_t *seed_material) {
  return csrng_send_app_cmd(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET,
                            (entropy_csrng_cmd_t){
                                .id = kEntropyDrbgOpReseed,
                                .disable_trng_input = disable_trng_input,
                                .seed_material = seed_material,
                                .generate_len = 0,
                            });
}

status_t entropy_csrng_update(const entropy_seed_material_t *seed_material) {
  return csrng_send_app_cmd(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET,
                            (entropy_csrng_cmd_t){
                                .id = kEntropyDrbgOpUpdate,
                                .seed_material = seed_material,
                                .generate_len = 0,
                            });
}

status_t entropy_csrng_generate_start(
    const entropy_seed_material_t *seed_material, size_t len) {
  // Round up the number of 128bit blocks. Aligning with respect to uint32_t.
  // TODO(#6112): Consider using a canonical reference for alignment operations.
  const uint32_t num_128bit_blocks = (len + 3) / 4;
  return csrng_send_app_cmd(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET,
                            (entropy_csrng_cmd_t){
                                .id = kEntropyDrbgOpGenerate,
                                .seed_material = seed_material,
                                .generate_len = num_128bit_blocks,
                            });
}

status_t entropy_csrng_generate_data_get(uint32_t *buf, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    // Block until there is more data available in the genbits buffer. CSRNG
    // generates data in 128bit chunks (i.e. 4 words).
    static_assert(kEntropyCsrngBitsBufferNumWords == 4,
                  "kEntropyCsrngBitsBufferNumWords must be a power of 2.");
    if (i & (kEntropyCsrngBitsBufferNumWords - 1)) {
      uint32_t reg;
      do {
        reg = abs_mmio_read32(kBaseCsrng + CSRNG_GENBITS_VLD_REG_OFFSET);
      } while (!bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT));
    }
    buf[i] = abs_mmio_read32(kBaseCsrng + CSRNG_GENBITS_REG_OFFSET);
  }
  return OK_STATUS();
}

status_t entropy_csrng_generate(const entropy_seed_material_t *seed_material,
                                uint32_t *buf, size_t len) {
  TRY(entropy_csrng_generate_start(seed_material, len));
  return entropy_csrng_generate_data_get(buf, len);
}

status_t entropy_csrng_uninstantiate(void) {
  return csrng_send_app_cmd(kBaseCsrng + CSRNG_CMD_REQ_REG_OFFSET,
                            (entropy_csrng_cmd_t){
                                .id = kEntropyDrbgOpUpdate,
                                .seed_material = NULL,
                                .generate_len = 0,
                            });
}
