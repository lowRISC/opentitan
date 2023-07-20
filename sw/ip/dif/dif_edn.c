// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_edn.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/dif/dif_csrng_shared.h"

#include "edn_regs.h"  // Generated

static dif_result_t check_locked(const dif_edn_t *edn) {
  if (mmio_region_read32(edn->base_addr, EDN_REGWEN_REG_OFFSET) == 0) {
    return kDifLocked;
  }
  return kDifOk;
}

dif_result_t dif_edn_configure(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(edn));

  uint32_t reg = mmio_region_read32(edn->base_addr, EDN_CTRL_REG_OFFSET);
  reg = bitfield_field32_write(reg, EDN_CTRL_EDN_ENABLE_FIELD,
                               kMultiBitBool4True);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_edn_lock(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(edn->base_addr, EDN_REGWEN_REG_OFFSET, 0);
  return kDifOk;
}

dif_result_t dif_edn_is_locked(const dif_edn_t *edn, bool *is_locked) {
  if (edn == NULL || is_locked == NULL) {
    return kDifBadArg;
  }
  *is_locked = check_locked(edn) != kDifOk;
  return kDifOk;
}

dif_result_t dif_edn_set_boot_mode(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(edn));

  uint32_t reg = mmio_region_read32(edn->base_addr, EDN_CTRL_REG_OFFSET);
  reg = bitfield_field32_write(reg, EDN_CTRL_BOOT_REQ_MODE_FIELD,
                               kMultiBitBool4True);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, reg);

  return kDifOk;
}

dif_result_t dif_edn_set_auto_mode(const dif_edn_t *edn,
                                   dif_edn_auto_params_t config) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(edn));

  // Check that EDN is disabled.  If it is not disabled (e.g., through a call
  // to `dif_edn_stop()`), we are not ready to change mode.
  uint32_t ctrl_reg = mmio_region_read32(edn->base_addr, EDN_CTRL_REG_OFFSET);
  const uint32_t edn_en =
      bitfield_field32_read(ctrl_reg, EDN_CTRL_EDN_ENABLE_FIELD);
  if (dif_multi_bit_bool_to_toggle(edn_en) != kDifToggleDisabled) {
    return kDifError;
  }

  // Ensure neither automatic nor boot request mode is set.
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_AUTO_REQ_MODE_FIELD,
                                    kMultiBitBool4False);
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_BOOT_REQ_MODE_FIELD,
                                    kMultiBitBool4False);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, ctrl_reg);

  // Clear the reseed command FIFO and the generate command FIFO.
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_CMD_FIFO_RST_FIELD,
                                    kMultiBitBool4True);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, ctrl_reg);

  // Restore command FIFOs to normal operation mode.  This is a prerequisite
  // before any further commands can be issued to these FIFOs.
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_CMD_FIFO_RST_FIELD,
                                    kMultiBitBool4False);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, ctrl_reg);

  // Fill the reseed command FIFO.
  mmio_region_write32(edn->base_addr, EDN_RESEED_CMD_REG_OFFSET,
                      config.reseed_cmd.cmd);
  for (size_t i = 0; i < config.reseed_cmd.seed_material.len; ++i) {
    mmio_region_write32(edn->base_addr, EDN_RESEED_CMD_REG_OFFSET,
                        config.reseed_cmd.seed_material.data[i]);
  }

  // Fill the generate command FIFO.
  mmio_region_write32(edn->base_addr, EDN_GENERATE_CMD_REG_OFFSET,
                      config.generate_cmd.cmd);
  for (size_t i = 0; i < config.generate_cmd.seed_material.len; ++i) {
    mmio_region_write32(edn->base_addr, EDN_GENERATE_CMD_REG_OFFSET,
                        config.generate_cmd.seed_material.data[i]);
  }

  // Set the maximum number of requests between reseeds.
  mmio_region_write32(edn->base_addr,
                      EDN_MAX_NUM_REQS_BETWEEN_RESEEDS_REG_OFFSET,
                      config.reseed_interval);

  // Re-enable EDN in automatic request mode.
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_EDN_ENABLE_FIELD,
                                    kMultiBitBool4True);
  ctrl_reg = bitfield_field32_write(ctrl_reg, EDN_CTRL_AUTO_REQ_MODE_FIELD,
                                    kMultiBitBool4True);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, ctrl_reg);

  // Wait until EDN is ready to accept commands.
  bool ready = false;
  while (!ready) {
    DIF_RETURN_IF_ERROR(dif_edn_get_status(edn, kDifEdnStatusReady, &ready));
  }

  // Command CSRNG Instantiate.  As soon as CSRNG acknowledges this command,
  // EDN will start automatically sending reseed and generate commands.
  const dif_edn_entropy_src_toggle_t entropy_src_enable =
      ((config.instantiate_cmd.cmd & 0xF00) >> 8) == kMultiBitBool4True
          ? kDifEdnEntropySrcToggleDisable
          : kDifEdnEntropySrcToggleEnable;
  DIF_RETURN_IF_ERROR(dif_edn_instantiate(
      edn, entropy_src_enable, &config.instantiate_cmd.seed_material));

  // Wait until CSRNG acknowledges command.
  ready = false;
  while (!ready) {
    DIF_RETURN_IF_ERROR(dif_edn_get_status(edn, kDifEdnStatusReady, &ready));
  }

  // Read request acknowledge error and return accordingly.
  bool ack_err;
  DIF_RETURN_IF_ERROR(dif_edn_get_status(edn, kDifEdnStatusCsrngAck, &ack_err));
  return ack_err ? kDifError : kDifOk;
}

dif_result_t dif_edn_get_status(const dif_edn_t *edn, dif_edn_status_t flag,
                                bool *set) {
  if (edn == NULL || set == NULL) {
    return kDifBadArg;
  }

  uint32_t bit;
  switch (flag) {
    case kDifEdnStatusReady:
      bit = EDN_SW_CMD_STS_CMD_RDY_BIT;
      break;
    case kDifEdnStatusCsrngAck:
      bit = EDN_SW_CMD_STS_CMD_STS_BIT;
      break;
    default:
      return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(edn->base_addr, EDN_SW_CMD_STS_REG_OFFSET);
  *set = bitfield_bit32_read(reg, bit);
  return kDifOk;
}

dif_result_t dif_edn_get_errors(const dif_edn_t *edn, uint32_t *unhealthy_fifos,
                                uint32_t *errors) {
  if (edn == NULL || unhealthy_fifos == NULL || errors == NULL) {
    return kDifBadArg;
  }
  *unhealthy_fifos = 0;
  *errors = 0;

  uint32_t reg = mmio_region_read32(edn->base_addr, EDN_ERR_CODE_REG_OFFSET);
  *unhealthy_fifos =
      bitfield_bit32_copy(*unhealthy_fifos, kDifEdnFifoReseedCmd, reg,
                          EDN_ERR_CODE_SFIFO_RESCMD_ERR_BIT);
  *unhealthy_fifos =
      bitfield_bit32_copy(*unhealthy_fifos, kDifEdnFifoGenerateCmd, reg,
                          EDN_ERR_CODE_SFIFO_GENCMD_ERR_BIT);

  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorAckSm, reg,
                                EDN_ERR_CODE_EDN_ACK_SM_ERR_BIT);
  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorMainSm, reg,
                                EDN_ERR_CODE_EDN_MAIN_SM_ERR_BIT);
  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorCounterFault, reg,
                                EDN_ERR_CODE_EDN_CNTR_ERR_BIT);
  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorFifoWrite, reg,
                                EDN_ERR_CODE_FIFO_WRITE_ERR_BIT);
  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorFifoRead, reg,
                                EDN_ERR_CODE_FIFO_READ_ERR_BIT);
  *errors = bitfield_bit32_copy(*errors, kDifEdnErrorFifoFullAndEmpty, reg,
                                EDN_ERR_CODE_FIFO_STATE_ERR_BIT);

  return kDifOk;
}

dif_result_t dif_edn_get_cmd_unhealthy_fifo_force(const dif_edn_t *edn,
                                                  dif_edn_fifo_t fifo) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  uint32_t fifo_bit;
  switch (fifo) {
    case kDifEdnFifoReseedCmd:
      fifo_bit = EDN_ERR_CODE_SFIFO_RESCMD_ERR_BIT;
      break;
    case kDifEdnFifoGenerateCmd:
      fifo_bit = EDN_ERR_CODE_SFIFO_GENCMD_ERR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  DIF_RETURN_IF_ERROR(check_locked(edn));
  mmio_region_write32(edn->base_addr, EDN_ERR_CODE_TEST_REG_OFFSET, fifo_bit);
  return kDifOk;
}

dif_result_t dif_edn_get_cmd_error_force(const dif_edn_t *edn,
                                         dif_edn_error_t error) {
  if (edn == NULL) {
    return kDifBadArg;
  }

  uint32_t error_bit;
  switch (error) {
    case kDifEdnErrorAckSm:
      error_bit = EDN_ERR_CODE_EDN_ACK_SM_ERR_BIT;
      break;
    case kDifEdnErrorMainSm:
      error_bit = EDN_ERR_CODE_EDN_MAIN_SM_ERR_BIT;
      break;
    case kDifEdnErrorCounterFault:
      error_bit = EDN_ERR_CODE_EDN_CNTR_ERR_BIT;
      break;
    case kDifEdnErrorFifoWrite:
      error_bit = EDN_ERR_CODE_FIFO_WRITE_ERR_BIT;
      break;
    case kDifEdnErrorFifoRead:
      error_bit = EDN_ERR_CODE_FIFO_READ_ERR_BIT;
      break;
    case kDifEdnErrorFifoFullAndEmpty:
      error_bit = EDN_ERR_CODE_FIFO_STATE_ERR_BIT;
      break;
    default:
      return kDifBadArg;
  }

  DIF_RETURN_IF_ERROR(check_locked(edn));
  mmio_region_write32(edn->base_addr, EDN_ERR_CODE_TEST_REG_OFFSET, error_bit);
  return kDifOk;
}

dif_result_t dif_edn_get_main_state_machine(const dif_edn_t *edn,
                                            uint32_t *state) {
  if (edn == NULL || state == NULL) {
    return kDifBadArg;
  }

  *state = mmio_region_read32(edn->base_addr, EDN_MAIN_SM_STATE_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_edn_instantiate(
    const dif_edn_t *edn, dif_edn_entropy_src_toggle_t entropy_src_enable,
    const dif_edn_seed_material_t *seed_material) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(
      edn->base_addr, EDN_SW_CMD_REQ_REG_OFFSET,
      (csrng_app_cmd_t){
          .id = kCsrngAppCmdInstantiate,
          .entropy_src_enable =
              (dif_csrng_entropy_src_toggle_t)entropy_src_enable,
          .seed_material = (const dif_csrng_seed_material_t *)seed_material,
      });
}

dif_result_t dif_edn_reseed(const dif_edn_t *edn,
                            const dif_edn_seed_material_t *seed_material) {
  if (edn == NULL || seed_material == NULL) {
    return kDifBadArg;
  }
  dif_csrng_seed_material_t seed_material2;
  memcpy(&seed_material2, seed_material, sizeof(seed_material2));
  return csrng_send_app_cmd(edn->base_addr, EDN_SW_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdReseed,
                                .seed_material = &seed_material2,
                            });
}

dif_result_t dif_edn_update(const dif_edn_t *edn,
                            const dif_edn_seed_material_t *seed_material) {
  if (edn == NULL || seed_material == NULL) {
    return kDifBadArg;
  }
  dif_csrng_seed_material_t seed_material2;
  memcpy(&seed_material2, seed_material, sizeof(seed_material2));
  return csrng_send_app_cmd(edn->base_addr, EDN_SW_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdUpdate,
                                .seed_material = &seed_material2,
                            });
}

dif_result_t dif_edn_generate_start(const dif_edn_t *edn, size_t len) {
  if (edn == NULL || len == 0) {
    return kDifBadArg;
  }

  // Round up the number of 128bit blocks. Aligning with respect to uint32_t.
  // TODO(#6112): Consider using a canonical reference for alignment operations.
  const uint32_t num_128bit_blocks = (len + 3) / 4;
  return csrng_send_app_cmd(edn->base_addr, EDN_SW_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdGenerate,
                                .generate_len = num_128bit_blocks,
                            });
}

dif_result_t dif_edn_uninstantiate(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  return csrng_send_app_cmd(edn->base_addr, EDN_SW_CMD_REQ_REG_OFFSET,
                            (csrng_app_cmd_t){
                                .id = kCsrngAppCmdUnisntantiate,
                            });
}

dif_result_t dif_edn_stop(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  DIF_RETURN_IF_ERROR(check_locked(edn));

  // Fifo clear is only honored if edn is enabled.
  uint32_t reg = mmio_region_read32(edn->base_addr, EDN_CTRL_REG_OFFSET);
  reg = bitfield_field32_write(reg, EDN_CTRL_CMD_FIFO_RST_FIELD,
                               kMultiBitBool4True);
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, reg);

  // Disable edn and restore Fifo clear at the same time so that no rogue
  // command can get in after the clear above.
  mmio_region_write32(edn->base_addr, EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);

  return kDifOk;
}

dif_result_t dif_edn_get_recoverable_alerts(const dif_edn_t *edn,
                                            uint32_t *alerts) {
  if (edn == NULL || alerts == NULL) {
    return kDifBadArg;
  }

  *alerts = 0;
  uint32_t reg =
      mmio_region_read32(edn->base_addr, EDN_RECOV_ALERT_STS_REG_OFFSET);
  *alerts = bitfield_bit32_copy(*alerts, kDifEdnRecoverableAlertBadEnable, reg,
                                EDN_RECOV_ALERT_STS_EDN_ENABLE_FIELD_ALERT_BIT);
  *alerts =
      bitfield_bit32_copy(*alerts, kDifEdnRecoverableAlertBadBootReqMode, reg,
                          EDN_RECOV_ALERT_STS_BOOT_REQ_MODE_FIELD_ALERT_BIT);
  *alerts =
      bitfield_bit32_copy(*alerts, kDifEdnRecoverableAlertBadAutoReqMode, reg,
                          EDN_RECOV_ALERT_STS_AUTO_REQ_MODE_FIELD_ALERT_BIT);
  *alerts =
      bitfield_bit32_copy(*alerts, kDifEdnRecoverableAlertBadFifoClear, reg,
                          EDN_RECOV_ALERT_STS_CMD_FIFO_RST_FIELD_ALERT_BIT);
  *alerts = bitfield_bit32_copy(*alerts, kDifEdnRecoverableAlertRepeatedGenBits,
                                reg, EDN_RECOV_ALERT_STS_EDN_BUS_CMP_ALERT_BIT);
  return kDifOk;
}

dif_result_t dif_edn_clear_recoverable_alerts(const dif_edn_t *edn) {
  if (edn == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(edn->base_addr, EDN_RECOV_ALERT_STS_REG_OFFSET, 0);
  return kDifOk;
}
