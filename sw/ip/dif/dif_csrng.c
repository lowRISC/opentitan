// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"

#include "csrng_regs.h"  // Generated

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
  if (csrng == NULL || seed_material == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdInstantiate,
                                .entropy_src_enable = entropy_src_enable,
                                .seed_material = seed_material,
                            });
}

dif_result_t dif_csrng_reseed(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  if (csrng == NULL || seed_material == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdReseed,
                                .seed_material = seed_material,
                            });
}

dif_result_t dif_csrng_update(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material) {
  if (csrng == NULL || seed_material == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdUpdate,
                                .seed_material = seed_material,
                            });
}

dif_result_t dif_csrng_generate_start(const dif_csrng_t *csrng, size_t len) {
  if (csrng == NULL || len == 0) {
    return kDifBadArg;
  }

  // Round up the number of 128bit blocks. Aligning with respect to uint32_t.
  // TODO(#6112): Consider using a canonical reference for alignment operations.
  const uint32_t num_128bit_blocks = (len + 3) / 4;
  return csrng_send_app_cmd(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
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
  if (csrng == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(csrng->base_addr, CSRNG_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
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

    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoCmd, reg,
                            CSRNG_ERR_CODE_SFIFO_CMD_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoGenBits, reg,
                            CSRNG_ERR_CODE_SFIFO_GENBITS_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoCmdReq, reg,
                            CSRNG_ERR_CODE_SFIFO_CMDREQ_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoRcStage, reg,
                            CSRNG_ERR_CODE_SFIFO_RCSTAGE_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoKeyVrc, reg,
                            CSRNG_ERR_CODE_SFIFO_KEYVRC_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoUpdateReq,
                            reg, CSRNG_ERR_CODE_SFIFO_UPDREQ_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoBencRec, reg,
                            CSRNG_ERR_CODE_SFIFO_BENCREQ_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoBencAck, reg,
                            CSRNG_ERR_CODE_SFIFO_BENCACK_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoPData, reg,
                            CSRNG_ERR_CODE_SFIFO_PDATA_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoFinal, reg,
                            CSRNG_ERR_CODE_SFIFO_FINAL_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoGBencAck, reg,
                            CSRNG_ERR_CODE_SFIFO_GBENCACK_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoGrcStage, reg,
                            CSRNG_ERR_CODE_SFIFO_GRCSTAGE_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoGGenReq, reg,
                            CSRNG_ERR_CODE_SFIFO_GGENREQ_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoGadStage, reg,
                            CSRNG_ERR_CODE_SFIFO_GADSTAGE_ERR_BIT);
    status->unhealthy_fifos =
        bitfield_bit32_copy(status->unhealthy_fifos, kDifCsrngFifoBlockEnc, reg,
                            CSRNG_ERR_CODE_SFIFO_BLKENC_ERR_BIT);

    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorCmdStageSm, reg,
                            CSRNG_ERR_CODE_CMD_STAGE_SM_ERR_BIT);
    status->errors = bitfield_bit32_copy(status->errors, kDifCsrngErrorMainSm,
                                         reg, CSRNG_ERR_CODE_MAIN_SM_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorDrbgGenSm, reg,
                            CSRNG_ERR_CODE_DRBG_GEN_SM_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorDrbgUpdateBlockEncSm,
                            reg, CSRNG_ERR_CODE_DRBG_UPDBE_SM_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorDrbgUpdateOutBlockSm,
                            reg, CSRNG_ERR_CODE_DRBG_UPDOB_SM_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorAesSm, reg,
                            CSRNG_ERR_CODE_AES_CIPHER_SM_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorGenerateCmdCounter,
                            reg, CSRNG_ERR_CODE_CMD_GEN_CNT_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorFifoWrite, reg,
                            CSRNG_ERR_CODE_FIFO_WRITE_ERR_BIT);
    status->errors = bitfield_bit32_copy(status->errors, kDifCsrngErrorFifoRead,
                                         reg, CSRNG_ERR_CODE_FIFO_READ_ERR_BIT);
    status->errors =
        bitfield_bit32_copy(status->errors, kDifCsrngErrorFifoFullAndEmpty, reg,
                            CSRNG_ERR_CODE_FIFO_STATE_ERR_BIT);

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
  uint32_t actual_reg =
      mmio_region_read32(csrng->base_addr, CSRNG_INT_STATE_NUM_REG_OFFSET);
  if (reg != actual_reg) {
    return kDifError;
  }

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

  *alerts =
      mmio_region_read32(csrng->base_addr, CSRNG_RECOV_ALERT_STS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_csrng_clear_recoverable_alerts(const dif_csrng_t *csrng) {
  if (csrng == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(csrng->base_addr, CSRNG_RECOV_ALERT_STS_REG_OFFSET, 0);
  return kDifOk;
}
