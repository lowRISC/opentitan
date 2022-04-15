// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "csrng_regs.h"  // Generated

enum {
  /**
   * CSRNG genbits buffer size in uint32_t words.
   */
  kCsrngGenBitsBufferSize = 4,
};

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
static dif_result_t write_application_command(const dif_csrng_t *csrng,
                                              const csrng_app_cmd_t *cmd) {
  if (csrng == NULL || cmd == NULL) {
    return kDifBadArg;
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
    return kDifBadArg;
  }

  // Build and write application command header.
  uint32_t reg = bitfield_field32_write(0, kAppCmdFieldCmdId, cmd->id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_bit32_write(reg, kAppCmdBitFlag0, cmd->entropy_src_enable);
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, cmd->generate_len);
  mmio_region_write32(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET, reg);

  for (size_t i = 0; i < cmd_len; ++i) {
    mmio_region_write32(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                        cmd->seed_material->seed_material[i]);
  }
  return kDifOk;
}

/**
 * Reads the output data register status.
 */
static void get_output_status(const dif_csrng_t *csrng,
                              dif_csrng_output_status_t *status) {
  uint32_t reg =
      mmio_region_read32(csrng->base_addr, CSRNG_GENBITS_VLD_REG_OFFSET);
  status->valid_data =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_VLD_BIT);
  status->fips_mode =
      bitfield_bit32_read(reg, CSRNG_GENBITS_VLD_GENBITS_FIPS_BIT);
}

/**
 * Returns true if the data register has valid data.
 */
static bool is_output_ready(const dif_csrng_t *csrng) {
  dif_csrng_output_status_t status;
  get_output_status(csrng, &status);
  return status.valid_data;
}

dif_result_t dif_csrng_configure(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      bitfield_field32_write(0, CSRNG_CTRL_ENABLE_FIELD, kMultiBitBool4True);
  reg = bitfield_field32_write(reg, CSRNG_CTRL_SW_APP_ENABLE_FIELD,
                               kMultiBitBool4True);
  reg = bitfield_field32_write(reg, CSRNG_CTRL_READ_INT_STATE_FIELD,
                               kMultiBitBool4True);
  mmio_region_write32(csrng->base_addr, CSRNG_CTRL_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_csrng_instantiate(
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

dif_result_t dif_csrng_reseed(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdReseed,
      .entropy_src_enable = false,
      .seed_material = seed_material,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_result_t dif_csrng_update(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdUpdate,
      .entropy_src_enable = false,
      .seed_material = seed_material,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_result_t dif_csrng_generate_start(const dif_csrng_t *csrng, size_t len) {
  if (len == 0) {
    return kDifBadArg;
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

dif_result_t dif_csrng_generate_end(const dif_csrng_t *csrng, uint32_t *buf,
                                    size_t len) {
  if (csrng == NULL || buf == NULL) {
    return kDifBadArg;
  }

  // Wait until there is data ready.
  while (!is_output_ready(csrng)) {
  }

  for (size_t i = 0, rd_cnt = 0; i < len; ++i, ++rd_cnt) {
    // Block until there is more data available in the genbits buffer.
    if (rd_cnt == kCsrngGenBitsBufferSize) {
      while (!is_output_ready(csrng)) {
      }
      rd_cnt = 0;
    }
    buf[i] = mmio_region_read32(csrng->base_addr, CSRNG_GENBITS_REG_OFFSET);
  }
  return kDifOk;
}

dif_result_t dif_csrng_uninstantiate(const dif_csrng_t *csrng) {
  const csrng_app_cmd_t app_cmd = {
      .id = kCsrngAppCmdUnisntantiate,
      .entropy_src_enable = false,
      .seed_material = NULL,
      .generate_len = 0,
  };
  return write_application_command(csrng, &app_cmd);
}

dif_result_t dif_csrng_get_cmd_interface_status(
    const dif_csrng_t *csrng, dif_csrng_cmd_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifBadArg;
  }

  uint32_t reg =
      mmio_region_read32(csrng->base_addr, CSRNG_SW_CMD_STS_REG_OFFSET);
  bool cmd_ready = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT);
  bool cmd_error = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_STS_BIT);

  // The function prioritizes error detection to avoid masking errors
  // when `cmd_ready` is set to true.
  if (cmd_error) {
    *status = kDifCsrngCmdStatusError;
    return kDifOk;
  }

  if (cmd_ready) {
    *status = kDifCsrngCmdStatusReady;
    return kDifOk;
  }

  *status = kDifCsrngCmdStatusBusy;
  return kDifOk;
}

dif_result_t dif_csrng_get_output_status(const dif_csrng_t *csrng,
                                         dif_csrng_output_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifBadArg;
  }
  get_output_status(csrng, status);
  return kDifOk;
}

OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_get_internal_state(
    const dif_csrng_t *csrng, dif_csrng_internal_state_id_t instance_id,
    dif_csrng_internal_state_t *state) {
  if (csrng == NULL || state == NULL) {
    return kDifBadArg;
  }

  // Select the instance id to read the internal state from, request a state
  // machine halt, and wait for the internal registers to be ready to be read.
  uint32_t reg = bitfield_field32_write(
      0, CSRNG_INT_STATE_NUM_INT_STATE_NUM_FIELD, instance_id);
  mmio_region_write32(csrng->base_addr, CSRNG_INT_STATE_NUM_REG_OFFSET, reg);

  // Read the internal state.
  state->reseed_counter =
      mmio_region_read32(csrng->base_addr, CSRNG_INT_STATE_VAL_REG_OFFSET);

  for (size_t i = 0; i < ARRAYSIZE(state->v); ++i) {
    state->v[i] =
        mmio_region_read32(csrng->base_addr, CSRNG_INT_STATE_VAL_REG_OFFSET);
  }

  for (size_t i = 0; i < ARRAYSIZE(state->key); ++i) {
    state->key[i] =
        mmio_region_read32(csrng->base_addr, CSRNG_INT_STATE_VAL_REG_OFFSET);
  }

  uint32_t flags =
      mmio_region_read32(csrng->base_addr, CSRNG_INT_STATE_VAL_REG_OFFSET);

  // The following bit indexes are defined in
  // https://docs.opentitan.org/hw/ip/csrng/doc/#working-state-values
  state->instantiated = bitfield_bit32_read(flags, /*bit_index=*/0u);
  state->fips_compliance = bitfield_bit32_read(flags, /*bit_index=*/1u);

  return kDifOk;
}

dif_result_t dif_csrng_stop(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(csrng->base_addr, CSRNG_CTRL_REG_OFFSET,
                      CSRNG_CTRL_REG_RESVAL);

  return kDifOk;
}
