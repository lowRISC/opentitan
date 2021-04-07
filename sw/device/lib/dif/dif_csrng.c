// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"

#include "csrng_regs.h"  // Generated

/**
 * Supported CSRNG application commands.
 * See https://docs.opentitan.org/hw/ip/csrng/doc/#command-header for
 * details.
 */
typedef enum csrng_app_cmd_id {
  kCsrngAppCmdInstantiate = 1,
  kCsrngAppCmdReseed = 2,
  kCsrngAppCmdGenerate = 3,
  kCsrngAppCmdUpdate = 4,
  kCsrngAppCmdUnisntantiate = 5,
} csrng_app_cmd_id_t;

/**
 * CSRNG application interface command header parameters.
 */
typedef struct csrng_app_cmd {
  /**
   * Application command.
   */
  csrng_app_cmd_id_t id;
  /**
   * Entropy source enable.
   *
   * Mapped to flag0 in the hardware command interface.
   */
  dif_csrng_entropy_src_toggle_t entropy_src_enable;
  /**
   * Seed material. Only used in `kCsrngAppCmdInstantiate`, `kCsrngAppCmdReseed`
   * and `kCsrngAppCmdUpdate` commands.
   */
  const dif_csrng_seed_material_t *seed_material;
  /**
   * Generate length. Specified as number of 128bit blocks.
   */
  uint32_t generate_len;
} csrng_app_cmd_t;

/**
 * Writes application command `cmd` to the CSRNG_CMD_REQ_REG register.
 * Returns the result of the operation.
 */
static dif_csrng_result_t write_application_command(
    const dif_csrng_t *csrng, const csrng_app_cmd_t *cmd) {
  if (csrng == NULL || cmd == NULL) {
    return kDifCsrngBadArg;
  }

  // The application command header is not specified as a register in the
  // hardware specification, so the fields are mapped here by hand. The
  // command register also accepts arbitrary 32bit data.
  const uint32_t kAppCmdBitFlag0 = 8;
  const bitfield_field32_t kAppCmdFieldCmdId = {.mask = 0xf, .index = 0};
  const bitfield_field32_t kAppCmdFieldCmdLen = {.mask = 0xf, .index = 4};
  const bitfield_field32_t kAppCmdFieldGlen = {.mask = 0x7ffff, .index = 12};

  uint32_t cmd_len =
      cmd->seed_material == NULL ? 0 : cmd->seed_material->seed_material_len;

  if (cmd_len & ~kAppCmdFieldCmdLen.mask) {
    return kDifCsrngBadArg;
  }

  // Build and write application command header.
  uint32_t reg = bitfield_field32_write(0, kAppCmdFieldCmdId, cmd->id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_bit32_write(reg, kAppCmdBitFlag0, cmd->entropy_src_enable);
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, cmd->generate_len);
  mmio_region_write32(csrng->params.base_addr, CSRNG_CMD_REQ_REG_OFFSET, reg);

  for (uint32_t i = 0; i < cmd_len; ++i) {
    mmio_region_write32(csrng->params.base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                        cmd->seed_material->seed_material[i]);
  }
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_init(dif_csrng_params_t params,
                                  dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifCsrngBadArg;
  }
  *csrng = (dif_csrng_t){.params = params};
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_configure(const dif_csrng_t *csrng,
                                       dif_csrng_config_t config) {
  if (csrng == NULL) {
    return kDifCsrngBadArg;
  }

  uint32_t reg = bitfield_bit32_write(0, CSRNG_CTRL_ENABLE_BIT, 1);
  reg = bitfield_bit32_write(reg, CSRNG_CTRL_AES_CIPHER_DISABLE_BIT,
                             config.debug_config.bypass_aes_cipher);

  // TODO: Determine if the dif library should support a diagnostics mode
  // of operation.
  reg = bitfield_field32_write(reg, CSRNG_CTRL_FIFO_DEPTH_STS_SEL_FIELD, 0);

  mmio_region_write32(csrng->params.base_addr, CSRNG_CTRL_REG_OFFSET, reg);
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_instantiate(
    const dif_csrng_t *csrng, dif_csrng_entropy_src_toggle_t entropy_src_enable,
    const dif_csrng_seed_material_t *seed_material) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdInstantiate,
      .entropy_src_enable = entropy_src_enable,
      .seed_material = seed_material,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_csrng_result_t dif_csrng_reseed(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *seed_material) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdReseed,
      .entropy_src_enable = false,
      .seed_material = seed_material,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_csrng_result_t dif_csrng_update(
    const dif_csrng_t *csrng, const dif_csrng_seed_material_t *seed_material) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdUpdate,
      .entropy_src_enable = false,
      .seed_material = seed_material,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_csrng_result_t dif_csrng_generate(const dif_csrng_t *csrng, size_t len) {
  if (len == 0) {
    return kDifCsrngBadArg;
  }

  // Round up the number of 128bit blocks. Aligning with respect to uint32_t.
  // TODO(#6112): Consider using a canonical reference for alignment operations.
  const uint32_t num_128bit_blocks = (len + 3) / 4;

  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdGenerate,
      .entropy_src_enable = false,
      .seed_material = NULL,
      .generate_len = num_128bit_blocks,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_csrng_result_t dif_csrng_uninstantiate(const dif_csrng_t *csrng) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdUnisntantiate,
      .entropy_src_enable = false,
      .seed_material = NULL,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_csrng_result_t dif_csrng_get_cmd_interface_status(
    const dif_csrng_t *csrng, dif_csrng_cmd_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifCsrngBadArg;
  }

  uint32_t reg =
      mmio_region_read32(csrng->params.base_addr, CSRNG_SW_CMD_STS_REG_OFFSET);
  bool cmd_ready = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT);
  bool cmd_error = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_STS_BIT);

  // The function prioritizes error detection to avoid masking errors
  // when `cmd_ready` is set to true.
  if (cmd_error) {
    *status = kDifCsrngCmdStatusError;
    return kDifCsrngOk;
  }

  if (cmd_ready) {
    *status = kDifCsrngCmdStatusReady;
    return kDifCsrngOk;
  }

  *status = kDifCsrngCmdStatusBusy;
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_get_output_status(
    const dif_csrng_t *csrng, dif_csrng_output_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifCsrngBadArg;
  }
  uint32_t reg =
      mmio_region_read32(csrng->params.base_addr, CSRNG_GENBITS_VLD_REG_OFFSET);
  status->valid_data =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  status->fips_mode =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_FIPS_BIT);
  return kDifCsrngOk;
}

dif_csrng_result_t dif_csrng_read_output(const dif_csrng_t *csrng,
                                         uint32_t *buf, size_t len) {
  if (csrng == NULL || buf == NULL) {
    return kDifCsrngBadArg;
  }

  for (uint32_t i = 0; i < len; ++i) {
    buf[i] =
        mmio_region_read32(csrng->params.base_addr, CSRNG_GENBITS_REG_OFFSET);
  }
  return kDifCsrngOk;
}
