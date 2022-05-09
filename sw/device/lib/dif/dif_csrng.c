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

#define BITSET_INSERT(set_, hw_idx_, dif_idx_) \
  set_ = bitfield_bit32_write(set_, dif_idx_, bitfield_bit32_read(reg, hw_idx_))

/**
 * Writes application command `cmd` to the CSRNG_CMD_REQ_REG register.
 * Returns the result of the operation.
 */
static dif_result_t write_application_command(const dif_csrng_t *csrng,
                                              csrng_app_cmd_t cmd) {
  if (csrng == NULL) {
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
      cmd.seed_material == NULL ? 0 : cmd.seed_material->seed_material_len;

  if (cmd_len & ~kAppCmdFieldCmdLen.mask) {
    return kDifBadArg;
  }

  // Build and write application command header.
  uint32_t reg = bitfield_field32_write(0, kAppCmdFieldCmdId, cmd.id);
  reg = bitfield_field32_write(reg, kAppCmdFieldCmdLen, cmd_len);
  reg = bitfield_bit32_write(reg, kAppCmdBitFlag0, cmd.entropy_src_enable);
  reg = bitfield_field32_write(reg, kAppCmdFieldGlen, cmd.generate_len);
  mmio_region_write32(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET, reg);

  for (size_t i = 0; i < cmd_len; ++i) {
    mmio_region_write32(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                        cmd.seed_material->seed_material[i]);
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
static void spin_until_ready(const dif_csrng_t *csrng) {
  dif_csrng_output_status_t status;
  do {
    get_output_status(csrng, &status);
  } while (!status.valid_data);
}

static dif_result_t check_locked(const dif_csrng_t *csrng) {
  if (mmio_region_read32(csrng->base_addr, CSRNG_REGWEN_REG_OFFSET) == 0) {
    return kDifLocked;
  }
  return kDifOk;
}

dif_result_t dif_csrng_configure(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(csrng));

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
  return write_application_command(csrng,
                                   (csrng_app_cmd_t){
                                       .id = kCsrngAppCmdInstantiate,
                                       .entropy_src_enable = entropy_src_enable,
                                       .seed_material = seed_material,
                                   });
}

dif_result_t dif_csrng_reseed(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  return write_application_command(csrng, (csrng_app_cmd_t){
                                              .id = kCsrngAppCmdReseed,
                                              .seed_material = seed_material,
                                          });
}

dif_result_t dif_csrng_update(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  return write_application_command(csrng, (csrng_app_cmd_t){
                                              .id = kCsrngAppCmdUpdate,
                                              .seed_material = seed_material,
                                          });
}

dif_result_t dif_csrng_generate_start(const dif_csrng_t *csrng, size_t len) {
  if (len == 0) {
    return kDifBadArg;
  }

  // Round up the number of 128bit blocks. Aligning with respect to uint32_t.
  // TODO(#6112): Consider using a canonical reference for alignment operations.
  const uint32_t num_128bit_blocks = (len + 3) / 4;
  return write_application_command(csrng, (csrng_app_cmd_t){
                                              .id = kCsrngAppCmdGenerate,
                                              .generate_len = num_128bit_blocks,
                                          });
}

dif_result_t dif_csrng_generate_read(const dif_csrng_t *csrng, uint32_t *buf,
                                     size_t len) {
  if (csrng == NULL || buf == NULL) {
    return kDifBadArg;
  }

  for (size_t i = 0; i < len; ++i) {
    // Block until there is more data available in the genbits buffer.
    if (i % kCsrngGenBitsBufferSize == 0) {
      spin_until_ready(csrng);
    }
    buf[i] = mmio_region_read32(csrng->base_addr, CSRNG_GENBITS_REG_OFFSET);
  }
  return kDifOk;
}

dif_result_t dif_csrng_uninstantiate(const dif_csrng_t *csrng) {
  return write_application_command(csrng, (csrng_app_cmd_t){
                                              .id = kCsrngAppCmdUnisntantiate,
                                          });
}

dif_result_t dif_csrng_get_cmd_interface_status(
    const dif_csrng_t *csrng, dif_csrng_cmd_status_t *status) {
  if (csrng == NULL || status == NULL) {
    return kDifBadArg;
  }
  *status = (dif_csrng_cmd_status_t){0};

  uint32_t reg =
      mmio_region_read32(csrng->base_addr, CSRNG_SW_CMD_STS_REG_OFFSET);
  bool cmd_ready = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT);
  bool cmd_error = bitfield_bit32_read(reg, CSRNG_SW_CMD_STS_CMD_STS_BIT);

  // The function prioritizes error detection to avoid masking errors
  // when `cmd_ready` is set to true.
  if (cmd_error) {
    status->kind = kDifCsrngCmdStatusError;
    uint32_t reg =
        mmio_region_read32(csrng->base_addr, CSRNG_ERR_CODE_REG_OFFSET);

    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_CMD_ERR_BIT,
                  kDifCsrngFifoCmd);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_GENBITS_ERR_BIT,
                  kDifCsrngFifoGenBits);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_CMDREQ_ERR_BIT,
                  kDifCsrngFifoCmdReq);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_RCSTAGE_ERR_BIT,
                  kDifCsrngFifoRcStage);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_KEYVRC_ERR_BIT,
                  kDifCsrngFifoKeyVrc);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_UPDREQ_ERR_BIT,
                  kDifCsrngFifoUpdateReq);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_BENCREQ_ERR_BIT,
                  kDifCsrngFifoBencRec);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_BENCACK_ERR_BIT,
                  kDifCsrngFifoBencAck);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_PDATA_ERR_BIT,
                  kDifCsrngFifoPData);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_FINAL_ERR_BIT,
                  kDifCsrngFifoFinal);
    BITSET_INSERT(status->unhealthy_fifos,
                  CSRNG_ERR_CODE_SFIFO_GBENCACK_ERR_BIT, kDifCsrngFifoGBencAck);
    BITSET_INSERT(status->unhealthy_fifos,
                  CSRNG_ERR_CODE_SFIFO_GRCSTAGE_ERR_BIT, kDifCsrngFifoGrcStage);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_GGENREQ_ERR_BIT,
                  kDifCsrngFifoGGenReq);
    BITSET_INSERT(status->unhealthy_fifos,
                  CSRNG_ERR_CODE_SFIFO_GADSTAGE_ERR_BIT, kDifCsrngFifoGadStage);
    BITSET_INSERT(status->unhealthy_fifos, CSRNG_ERR_CODE_SFIFO_BLKENC_ERR_BIT,
                  kDifCsrngFifoBlockEnc);

    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_CMD_STAGE_SM_ERR_BIT,
                  kDifCsrngErrorCmdStageSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_MAIN_SM_ERR_BIT,
                  kDifCsrngErrorMainSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_DRBG_GEN_SM_ERR_BIT,
                  kDifCsrngErrorDrbgGenSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_DRBG_UPDBE_SM_ERR_BIT,
                  kDifCsrngErrorDrbgUpdateBlockEncSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_DRBG_UPDOB_SM_ERR_BIT,
                  kDifCsrngErrorDrbgUpdateOutBlockSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_AES_CIPHER_SM_ERR_BIT,
                  kDifCsrngErrorAesSm);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_CMD_GEN_CNT_ERR_BIT,
                  kDifCsrngErrorGenerateCmdCounter);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_FIFO_WRITE_ERR_BIT,
                  kDifCsrngErrorFifoWrite);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_FIFO_READ_ERR_BIT,
                  kDifCsrngErrorFifoRead);
    BITSET_INSERT(status->errors, CSRNG_ERR_CODE_FIFO_STATE_ERR_BIT,
                  kDifCsrngErrorFifoFullAndEmpty);

    return kDifOk;
  }

  if (cmd_ready) {
    status->kind = kDifCsrngCmdStatusReady;
    return kDifOk;
  }

  status->kind = kDifCsrngCmdStatusBusy;
  return kDifOk;
}

dif_result_t dif_csrng_get_cmd_force_unhealthy_fifo(const dif_csrng_t *csrng,
                                                    dif_csrng_fifo_t fifo) {
  if (csrng == NULL) {
    return kDifBadArg;
  }

  uint32_t fifo_bit;
  switch (fifo) {
    case kDifCsrngFifoCmd:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_CMD_ERR_BIT;
      break;
    case kDifCsrngFifoGenBits:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_GENBITS_ERR_BIT;
      break;
    case kDifCsrngFifoCmdReq:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_CMDREQ_ERR_BIT;
      break;
    case kDifCsrngFifoRcStage:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_RCSTAGE_ERR_BIT;
      break;
    case kDifCsrngFifoKeyVrc:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_KEYVRC_ERR_BIT;
      break;
    case kDifCsrngFifoUpdateReq:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_UPDREQ_ERR_BIT;
      break;
    case kDifCsrngFifoBencRec:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_BENCREQ_ERR_BIT;
      break;
    case kDifCsrngFifoBencAck:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_BENCACK_ERR_BIT;
      break;
    case kDifCsrngFifoPData:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_PDATA_ERR_BIT;
      break;
    case kDifCsrngFifoFinal:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_FINAL_ERR_BIT;
      break;
    case kDifCsrngFifoGBencAck:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_GBENCACK_ERR_BIT;
      break;
    case kDifCsrngFifoGrcStage:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_GRCSTAGE_ERR_BIT;
      break;
    case kDifCsrngFifoGGenReq:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_GGENREQ_ERR_BIT;
      break;
    case kDifCsrngFifoGadStage:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_GADSTAGE_ERR_BIT;
      break;
    case kDifCsrngFifoBlockEnc:
      fifo_bit = CSRNG_ERR_CODE_SFIFO_BLKENC_ERR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  DIF_RETURN_IF_ERROR(check_locked(csrng));
  mmio_region_write32(csrng->base_addr, CSRNG_ERR_CODE_TEST_REG_OFFSET,
                      fifo_bit);
  return kDifOk;
}

dif_result_t dif_csrng_get_cmd_force_error(const dif_csrng_t *csrng,
                                           dif_csrng_error_t error) {
  if (csrng == NULL) {
    return kDifBadArg;
  }

  uint32_t error_bit;
  switch (error) {
    case kDifCsrngErrorCmdStageSm:
      error_bit = CSRNG_ERR_CODE_CMD_STAGE_SM_ERR_BIT;
      break;
    case kDifCsrngErrorMainSm:
      error_bit = CSRNG_ERR_CODE_MAIN_SM_ERR_BIT;
      break;
    case kDifCsrngErrorDrbgGenSm:
      error_bit = CSRNG_ERR_CODE_DRBG_GEN_SM_ERR_BIT;
      break;
    case kDifCsrngErrorDrbgUpdateBlockEncSm:
      error_bit = CSRNG_ERR_CODE_DRBG_UPDBE_SM_ERR_BIT;
      break;
    case kDifCsrngErrorDrbgUpdateOutBlockSm:
      error_bit = CSRNG_ERR_CODE_DRBG_UPDOB_SM_ERR_BIT;
      break;
    case kDifCsrngErrorAesSm:
      error_bit = CSRNG_ERR_CODE_AES_CIPHER_SM_ERR_BIT;
      break;
    case kDifCsrngErrorGenerateCmdCounter:
      error_bit = CSRNG_ERR_CODE_CMD_GEN_CNT_ERR_BIT;
      break;
    case kDifCsrngErrorFifoWrite:
      error_bit = CSRNG_ERR_CODE_FIFO_WRITE_ERR_BIT;
      break;
    case kDifCsrngErrorFifoRead:
      error_bit = CSRNG_ERR_CODE_FIFO_READ_ERR_BIT;
      break;
    case kDifCsrngErrorFifoFullAndEmpty:
      error_bit = CSRNG_ERR_CODE_FIFO_STATE_ERR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  DIF_RETURN_IF_ERROR(check_locked(csrng));
  mmio_region_write32(csrng->base_addr, CSRNG_ERR_CODE_TEST_REG_OFFSET,
                      error_bit);
  return kDifOk;
}

dif_result_t dif_csrng_get_main_state_machine(const dif_csrng_t *csrng,
                                              uint32_t *state) {
  if (csrng == NULL || state == NULL) {
    return kDifBadArg;
  }

  *state = mmio_region_read32(csrng->base_addr, CSRNG_MAIN_SM_STATE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_csrng_get_hw_csrng_exceptions(const dif_csrng_t *csrng,
                                               uint32_t *exceptions) {
  if (csrng == NULL || exceptions == NULL) {
    return kDifBadArg;
  }

  *exceptions =
      mmio_region_read32(csrng->base_addr, CSRNG_HW_EXC_STS_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_csrng_clear_hw_csrng_exceptions(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(csrng->base_addr, CSRNG_HW_EXC_STS_REG_OFFSET, 0);
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

dif_result_t dif_csrng_lock(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(csrng->base_addr, CSRNG_REGWEN_REG_OFFSET, 0);
  return kDifOk;
}

dif_result_t dif_csrng_is_locked(const dif_csrng_t *csrng, bool *is_locked) {
  if (csrng == NULL || is_locked == NULL) {
    return kDifBadArg;
  }
  *is_locked = check_locked(csrng) != kDifOk;
  return kDifOk;
}

dif_result_t dif_csrng_stop(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(csrng));
  mmio_region_write32(csrng->base_addr, CSRNG_CTRL_REG_OFFSET,
                      CSRNG_CTRL_REG_RESVAL);
  return kDifOk;
}

dif_result_t dif_csrng_get_recoverable_alerts(const dif_csrng_t *csrng,
                                              uint32_t *alerts) {
  if (csrng == NULL || alerts == NULL) {
    return kDifBadArg;
  }
  uint32_t reg =
      mmio_region_read32(csrng->base_addr, CSRNG_RECOV_ALERT_STS_REG_OFFSET);
  BITSET_INSERT(*alerts, CSRNG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_BIT,
                kDifCsrngRecoverableAlertBadEnable);
  BITSET_INSERT(*alerts, CSRNG_RECOV_ALERT_STS_SW_APP_ENABLE_FIELD_ALERT_BIT,
                kDifCsrngRecoverableAlertBadSwAppEnable);
  BITSET_INSERT(*alerts, CSRNG_RECOV_ALERT_STS_READ_INT_STATE_FIELD_ALERT_BIT,
                kDifCsrngRecoverableAlertBadIntState);
  BITSET_INSERT(*alerts, CSRNG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_BIT,
                kDifCsrngRecoverableAlertRepeatedGenBits);
  return kDifOk;
}

dif_result_t dif_csrng_clear_recoverable_alerts(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(csrng->base_addr, CSRNG_RECOV_ALERT_STS_REG_OFFSET, 0);
  return kDifOk;
}
