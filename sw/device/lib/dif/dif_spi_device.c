// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_base.h"

#include "spi_device_regs.h"  // Generated.

#define DIF_SPI_DEVICE_TPM_FIFO_DEPTH 16

enum {
  kDifSpiDeviceEFlashLen =
      SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH * sizeof(uint32_t),
  kDifSpiDeviceMailboxLen =
      SPI_DEVICE_PARAM_SRAM_MAILBOX_DEPTH * sizeof(uint32_t),
  kDifSpiDeviceSfdpLen = SPI_DEVICE_PARAM_SRAM_SFDP_DEPTH * sizeof(uint32_t),
  kDifSpiDevicePayloadLen =
      SPI_DEVICE_PARAM_SRAM_PAYLOAD_DEPTH * sizeof(uint32_t),
  kDifSpiDeviceTpmWriteFifoLen =
      SPI_DEVICE_PARAM_SRAM_TPM_WR_FIFO_DEPTH * sizeof(uint32_t),
};

enum {
  kDifSpiDeviceEFlashOffset =
      SPI_DEVICE_PARAM_SRAM_READ_BUFFER_OFFSET * sizeof(uint32_t),
  kDifSpiDeviceMailboxOffset =
      SPI_DEVICE_PARAM_SRAM_MAILBOX_OFFSET * sizeof(uint32_t),
  kDifSpiDeviceSfdpOffset =
      SPI_DEVICE_PARAM_SRAM_SFDP_OFFSET * sizeof(uint32_t),
  kDifSpiDevicePayloadOffset =
      SPI_DEVICE_PARAM_SRAM_PAYLOAD_OFFSET * sizeof(uint32_t),
  kDifSpiDeviceTpmWriteFifoOffset =
      SPI_DEVICE_PARAM_SRAM_TPM_WR_FIFO_OFFSET * sizeof(uint32_t),
};

/**
 * Computes the required value of the control register from a given
 * configuration.
 */
static inline uint32_t build_control_word(
    const dif_spi_device_config_t config) {
  uint32_t val = 0;

  val = bitfield_bit32_write(val, SPI_DEVICE_CFG_TX_ORDER_BIT,
                             config.tx_order == kDifSpiDeviceBitOrderLsbToMsb);
  val = bitfield_bit32_write(val, SPI_DEVICE_CFG_RX_ORDER_BIT,
                             config.rx_order == kDifSpiDeviceBitOrderLsbToMsb);

  return val;
}

/**
 * Extracts the mode value from the given configuration. Return all ones if the
 * configuration is invalid.
 */
static inline uint32_t extract_mode_from_config(
    const dif_spi_device_config_t config) {
  switch (config.device_mode) {
    case kDifSpiDeviceModeDisabled:
      return SPI_DEVICE_CONTROL_MODE_VALUE_DISABLED;
    case kDifSpiDeviceModeFlashEmulation:
      return SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE;
    case kDifSpiDeviceModePassthrough:
      return SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH;
    default:
      return -1u;
  }
  return -1u;
}

dif_result_t dif_spi_device_init_handle(mmio_region_t base_addr,
                                        dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  return dif_spi_device_init(base_addr, &spi->dev);
}

dif_result_t dif_spi_device_init_handle_from_dt(dt_spi_device_t dt,
                                                dif_spi_device_handle_t *spi) {
  mmio_region_t addr =
      mmio_region_from_addr(dt_spi_device_primary_reg_block(dt));
  return dif_spi_device_init_handle(addr, spi);
}

dif_result_t dif_spi_device_configure(dif_spi_device_handle_t *spi,
                                      dif_spi_device_config_t config) {
  if (spi == NULL) {
    return kDifBadArg;
  }

  uint32_t device_mode = extract_mode_from_config(config);
  if (device_mode == -1u) {
    return kDifBadArg;
  }

  uint32_t device_config = build_control_word(config);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET,
                      device_config);

  uint32_t control =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET);
  // Change mode.
  control = bitfield_field32_write(control, SPI_DEVICE_CONTROL_MODE_FIELD,
                                   device_mode);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                      control);

  spi->config = config;
  return kDifOk;
}

dif_result_t dif_spi_device_set_passthrough_mode(dif_spi_device_handle_t *spi,
                                                 dif_toggle_t enable) {
  if (spi == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  uint32_t control =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET);
  uint32_t mode = bitfield_field32_read(control, SPI_DEVICE_CONTROL_MODE_FIELD);
  if (mode != SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE &&
      mode != SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH) {
    return kDifBadArg;
  }
  if (dif_toggle_to_bool(enable)) {
    control = bitfield_field32_write(control, SPI_DEVICE_CONTROL_MODE_FIELD,
                                     SPI_DEVICE_CONTROL_MODE_VALUE_PASSTHROUGH);
  } else {
    control = bitfield_field32_write(control, SPI_DEVICE_CONTROL_MODE_FIELD,
                                     SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE);
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                      control);
  return kDifOk;
}

dif_result_t dif_spi_device_get_csb_status(dif_spi_device_handle_t *spi,
                                           bool *csb) {
  if (spi == NULL || csb == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_STATUS_REG_OFFSET);
  *csb = bitfield_bit32_read(reg_val, SPI_DEVICE_STATUS_CSB_BIT);
  return kDifOk;
}

dif_result_t dif_spi_device_enable_mailbox(dif_spi_device_handle_t *spi,
                                           uint32_t address) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_MAILBOX_ADDR_REG_OFFSET,
                      address);
  uint32_t cfg_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, SPI_DEVICE_CFG_MAILBOX_EN_BIT, 1);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET, cfg_reg);
  return kDifOk;
}

dif_result_t dif_spi_device_disable_mailbox(dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  uint32_t cfg_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET);
  cfg_reg = bitfield_bit32_write(cfg_reg, SPI_DEVICE_CFG_MAILBOX_EN_BIT, 0);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET, cfg_reg);
  return kDifOk;
}

dif_result_t dif_spi_device_get_mailbox_configuration(
    dif_spi_device_handle_t *spi, dif_toggle_t *is_enabled, uint32_t *address) {
  if (spi == NULL || is_enabled == NULL || address == NULL) {
    return kDifBadArg;
  }
  uint32_t cfg_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_CFG_REG_OFFSET);
  bool mailbox_enabled =
      bitfield_bit32_read(cfg_reg, SPI_DEVICE_CFG_MAILBOX_EN_BIT);
  *is_enabled = dif_bool_to_toggle(mailbox_enabled);
  *address = mmio_region_read32(spi->dev.base_addr,
                                SPI_DEVICE_MAILBOX_ADDR_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_spi_device_set_4b_address_mode(dif_spi_device_handle_t *spi,
                                                dif_toggle_t addr_4b) {
  if (spi == NULL || !dif_is_valid_toggle(addr_4b)) {
    return kDifBadArg;
  }
  uint32_t cfg_reg = 0;
  if (addr_4b == kDifToggleEnabled) {
    cfg_reg = bitfield_bit32_write(cfg_reg, SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT,
                                   true);
  } else {
    cfg_reg = bitfield_bit32_write(cfg_reg, SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT,
                                   false);
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_ADDR_MODE_REG_OFFSET,
                      cfg_reg);
  return kDifOk;
}

dif_result_t dif_spi_device_get_4b_address_mode(dif_spi_device_handle_t *spi,
                                                dif_toggle_t *addr_4b) {
  if (spi == NULL || addr_4b == NULL) {
    return kDifBadArg;
  }
  uint32_t cfg_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_ADDR_MODE_REG_OFFSET);
  if (bitfield_bit32_read(cfg_reg, SPI_DEVICE_ADDR_MODE_ADDR_4B_EN_BIT)) {
    *addr_4b = kDifToggleEnabled;
  } else {
    *addr_4b = kDifToggleDisabled;
  }
  return kDifOk;
}

dif_result_t dif_spi_device_clear_flash_status_request(
    dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }

  uint32_t device_mode = extract_mode_from_config(spi->config);
  if (device_mode == -1u) {
    return kDifBadArg;
  }

  uint32_t control =
      bitfield_field32_write(0, SPI_DEVICE_CONTROL_MODE_FIELD, device_mode);
  control = bitfield_bit32_write(
      control, SPI_DEVICE_CONTROL_FLASH_STATUS_FIFO_CLR_BIT, true);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                      control);

  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_id(dif_spi_device_handle_t *spi,
                                         dif_spi_device_flash_id_t *id) {
  if (spi == NULL || id == NULL) {
    return kDifBadArg;
  }
  uint32_t cc_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_JEDEC_CC_REG_OFFSET);
  uint32_t id_reg =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_JEDEC_ID_REG_OFFSET);
  id->num_continuation_code =
      (uint8_t)bitfield_field32_read(cc_reg, SPI_DEVICE_JEDEC_CC_NUM_CC_FIELD);
  id->continuation_code =
      (uint8_t)bitfield_field32_read(cc_reg, SPI_DEVICE_JEDEC_CC_CC_FIELD);
  id->manufacturer_id =
      (uint8_t)bitfield_field32_read(id_reg, SPI_DEVICE_JEDEC_ID_MF_FIELD);
  id->device_id =
      (uint16_t)bitfield_field32_read(id_reg, SPI_DEVICE_JEDEC_ID_ID_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_set_flash_id(dif_spi_device_handle_t *spi,
                                         dif_spi_device_flash_id_t id) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  uint32_t cc_reg = bitfield_field32_write(0, SPI_DEVICE_JEDEC_CC_NUM_CC_FIELD,
                                           id.num_continuation_code);
  cc_reg = bitfield_field32_write(cc_reg, SPI_DEVICE_JEDEC_CC_CC_FIELD,
                                  id.continuation_code);
  uint32_t id_reg = bitfield_field32_write(0, SPI_DEVICE_JEDEC_ID_MF_FIELD,
                                           id.manufacturer_id);
  id_reg = bitfield_field32_write(id_reg, SPI_DEVICE_JEDEC_ID_ID_FIELD,
                                  id.device_id);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_JEDEC_CC_REG_OFFSET,
                      cc_reg);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_JEDEC_ID_REG_OFFSET,
                      id_reg);
  return kDifOk;
}

dif_result_t dif_spi_device_set_passthrough_intercept_config(
    dif_spi_device_handle_t *spi,
    dif_spi_device_passthrough_intercept_config_t config) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = bitfield_bit32_write(0, SPI_DEVICE_INTERCEPT_EN_STATUS_BIT,
                                          config.status);
  reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_INTERCEPT_EN_JEDEC_BIT,
                                 config.jedec_id);
  reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_INTERCEPT_EN_SFDP_BIT,
                                 config.sfdp);
  reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_INTERCEPT_EN_MBX_BIT,
                                 config.mailbox);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_INTERCEPT_EN_REG_OFFSET,
                      reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_get_last_read_address(dif_spi_device_handle_t *spi,
                                                  uint32_t *address) {
  if (spi == NULL || address == NULL) {
    return kDifBadArg;
  }
  *address = mmio_region_read32(spi->dev.base_addr,
                                SPI_DEVICE_LAST_READ_ADDR_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_spi_device_set_eflash_read_threshold(
    dif_spi_device_handle_t *spi, uint32_t address) {
  if (spi == NULL || address > SPI_DEVICE_READ_THRESHOLD_THRESHOLD_MASK) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_READ_THRESHOLD_REG_OFFSET,
                      address);
  return kDifOk;
}

dif_result_t dif_spi_device_reset_eflash_buffer(dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }

  uint32_t device_mode = extract_mode_from_config(spi->config);
  if (device_mode == -1u) {
    return kDifBadArg;
  }

  uint32_t control =
      bitfield_field32_write(0, SPI_DEVICE_CONTROL_MODE_FIELD, device_mode);
  control = bitfield_bit32_write(
      control, SPI_DEVICE_CONTROL_FLASH_READ_BUFFER_CLR_BIT, true);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_CONTROL_REG_OFFSET,
                      control);

  return kDifOk;
}

dif_result_t dif_spi_device_set_flash_command_slot(
    dif_spi_device_handle_t *spi, uint8_t slot, dif_toggle_t enable,
    dif_spi_device_flash_command_t command_info) {
  if (spi == NULL || slot >= SPI_DEVICE_PARAM_NUM_CMD_INFO ||
      !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  ptrdiff_t reg_offset =
      SPI_DEVICE_CMD_INFO_0_REG_OFFSET + slot * sizeof(uint32_t);
  uint32_t reg_val = 0;
  if (enable == kDifToggleDisabled) {
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_VALID_0_BIT, false);
  } else {
    // Validate command info parameters.
    uint32_t address_mode;
    switch (command_info.address_type) {
      case kDifSpiDeviceFlashAddrDisabled:
        address_mode = SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRDISABLED;
        break;
      case kDifSpiDeviceFlashAddrCfg:
        address_mode = SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRCFG;
        break;
      case kDifSpiDeviceFlashAddr3Byte:
        address_mode = SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B;
        break;
      case kDifSpiDeviceFlashAddr4Byte:
        address_mode = SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR4B;
        break;
      default:
        return kDifBadArg;
    }
    if (command_info.dummy_cycles >
        (1u + SPI_DEVICE_CMD_INFO_0_DUMMY_SIZE_0_MASK)) {
      return kDifBadArg;
    }

    uint32_t payload_en;
    switch (command_info.payload_io_type) {
      case kDifSpiDevicePayloadIoNone:
        payload_en = 0x0;
        break;
      case kDifSpiDevicePayloadIoSingle:
        if (command_info.payload_dir_to_host) {
          payload_en = 0x2;
        } else {
          payload_en = 0x1;
        }
        break;
      case kDifSpiDevicePayloadIoDual:
        payload_en = 0x3;
        break;
      case kDifSpiDevicePayloadIoQuad:
        payload_en = 0xf;
        break;
      default:
        return kDifBadArg;
    }

    uint32_t read_pipeline_mode;
    switch (command_info.read_pipeline_mode) {
      case kDifSpiDeviceReadPipelineModeZeroStages:
        read_pipeline_mode =
            SPI_DEVICE_CMD_INFO_0_READ_PIPELINE_MODE_0_VALUE_ZERO_STAGES;
        break;
      case kDifSpiDeviceReadPipelineModeTwoStagesHalfCycle:
        read_pipeline_mode =
            SPI_DEVICE_CMD_INFO_0_READ_PIPELINE_MODE_0_VALUE_TWO_STAGES_HALF_CYCLE;
        break;
      case kDifSpiDeviceReadPipelineModeTwoStagesFullCycle:
        read_pipeline_mode =
            SPI_DEVICE_CMD_INFO_0_READ_PIPELINE_MODE_0_VALUE_TWO_STAGES_FULL_CYCLE;
        break;
      default:
        return kDifBadArg;
    }

    // Check for invalid argument combinations.
    if (command_info.payload_swap_enable &&
        (command_info.payload_dir_to_host ||
         command_info.payload_io_type != kDifSpiDevicePayloadIoSingle)) {
      return kDifBadArg;
    }
    if (command_info.passthrough_swap_address &&
        command_info.address_type == kDifSpiDeviceFlashAddrDisabled) {
      return kDifBadArg;
    }

    // Write the command info values.
    reg_val = bitfield_field32_write(
        reg_val, SPI_DEVICE_CMD_INFO_0_OPCODE_0_FIELD, command_info.opcode);
    reg_val = bitfield_field32_write(
        reg_val, SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_FIELD, address_mode);
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_ADDR_SWAP_EN_0_BIT,
                             command_info.passthrough_swap_address);
    if (command_info.dummy_cycles > 0) {
      reg_val = bitfield_field32_write(reg_val,
                                       SPI_DEVICE_CMD_INFO_0_DUMMY_SIZE_0_FIELD,
                                       command_info.dummy_cycles - 1);
      reg_val = bitfield_bit32_write(
          reg_val, SPI_DEVICE_CMD_INFO_0_DUMMY_EN_0_BIT, true);
    }
    reg_val = bitfield_field32_write(
        reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_EN_0_FIELD, payload_en);
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_DIR_0_BIT,
                             command_info.payload_dir_to_host);
    reg_val = bitfield_bit32_write(reg_val,
                                   SPI_DEVICE_CMD_INFO_0_PAYLOAD_SWAP_EN_0_BIT,
                                   command_info.payload_swap_enable);
    reg_val = bitfield_field32_write(
        reg_val, SPI_DEVICE_CMD_INFO_0_READ_PIPELINE_MODE_0_FIELD,
        read_pipeline_mode);
    reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_UPLOAD_0_BIT,
                                   command_info.upload);
    reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_BUSY_0_BIT,
                                   command_info.set_busy_status);
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_0_VALID_0_BIT, true);
  }
  mmio_region_write32(spi->dev.base_addr, reg_offset, reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_command_slot(
    dif_spi_device_handle_t *spi, uint8_t slot, dif_toggle_t *enabled,
    dif_spi_device_flash_command_t *command_info) {
  if (spi == NULL || enabled == NULL || command_info == NULL ||
      slot >= SPI_DEVICE_PARAM_NUM_CMD_INFO) {
    return kDifBadArg;
  }
  ptrdiff_t reg_offset =
      SPI_DEVICE_CMD_INFO_0_REG_OFFSET + slot * sizeof(uint32_t);
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr, reg_offset);

  dif_spi_device_flash_address_type_t address_type;
  uint32_t reg_val_address_mode =
      bitfield_field32_read(reg_val, SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_FIELD);
  switch (reg_val_address_mode) {
    case SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRDISABLED:
      address_type = kDifSpiDeviceFlashAddrDisabled;
      break;
    case SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDRCFG:
      address_type = kDifSpiDeviceFlashAddrCfg;
      break;
    case SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR3B:
      address_type = kDifSpiDeviceFlashAddr3Byte;
      break;
    case SPI_DEVICE_CMD_INFO_0_ADDR_MODE_0_VALUE_ADDR4B:
      address_type = kDifSpiDeviceFlashAddr4Byte;
      break;
    default:
      address_type = kDifSpiDeviceFlashAddrCount;
      break;
  }

  uint32_t dummy_cycles = 0;
  if (bitfield_bit32_read(reg_val, SPI_DEVICE_CMD_INFO_0_DUMMY_EN_0_BIT)) {
    dummy_cycles = 1 + bitfield_field32_read(
                           reg_val, SPI_DEVICE_CMD_INFO_0_DUMMY_SIZE_0_FIELD);
  } else {
    dummy_cycles = 0;
  }

  uint32_t payload_en =
      bitfield_field32_read(reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_EN_0_FIELD);
  bool payload_dir_to_host =
      bitfield_bit32_read(reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_DIR_0_BIT);
  dif_spi_device_payload_io_t payload_io_type;
  switch (payload_en) {
    case 0x0:
      payload_io_type = kDifSpiDevicePayloadIoNone;
      break;
    case 0x1:
      if (payload_dir_to_host) {
        payload_io_type = kDifSpiDevicePayloadIoInvalid;
      } else {
        payload_io_type = kDifSpiDevicePayloadIoSingle;
      }
      break;
    case 0x2:
      if (!payload_dir_to_host) {
        payload_io_type = kDifSpiDevicePayloadIoInvalid;
      } else {
        payload_io_type = kDifSpiDevicePayloadIoSingle;
      }
      break;
    case 0x3:
      payload_io_type = kDifSpiDevicePayloadIoDual;
      break;
    case 0xf:
      payload_io_type = kDifSpiDevicePayloadIoQuad;
      break;
    default:
      payload_io_type = kDifSpiDevicePayloadIoInvalid;
      break;
  }

  dif_spi_device_flash_command_t cmd = {
      .opcode = (uint8_t)bitfield_field32_read(
          reg_val, SPI_DEVICE_CMD_INFO_0_OPCODE_0_FIELD),
      .address_type = address_type,
      .dummy_cycles = (uint8_t)dummy_cycles,
      .payload_io_type = payload_io_type,
      .passthrough_swap_address = bitfield_bit32_read(
          reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_SWAP_EN_0_BIT),
      .payload_dir_to_host = payload_dir_to_host,
      .payload_swap_enable = bitfield_bit32_read(
          reg_val, SPI_DEVICE_CMD_INFO_0_PAYLOAD_SWAP_EN_0_BIT),
      .upload =
          bitfield_bit32_read(reg_val, SPI_DEVICE_CMD_INFO_0_UPLOAD_0_BIT),
      .set_busy_status =
          bitfield_bit32_read(reg_val, SPI_DEVICE_CMD_INFO_0_BUSY_0_BIT),
  };
  *command_info = cmd;

  if (bitfield_bit32_read(reg_val, SPI_DEVICE_CMD_INFO_0_VALID_0_BIT)) {
    *enabled = kDifToggleEnabled;
  } else {
    *enabled = kDifToggleDisabled;
  }
  return kDifOk;
}

/**
 * Write cmd_info register that is a separate CSR for a specific opcode (not
 * attached to a numbered slot).
 *
 * @param spi A handle to a spi_device.
 * @param enable Whether to enable the function.
 * @param opcode Which opcode activates the function.
 * @param reg_offset The register offset for the function's cmd_info CSR.
 * @return The result of the operation.
 */
static dif_result_t write_special_cmd_info(dif_spi_device_handle_t *spi,
                                           dif_toggle_t enable, uint8_t opcode,
                                           ptrdiff_t reg_offset) {
  if (spi == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  bool valid = dif_toggle_to_bool(enable);
  uint32_t reg_val =
      bitfield_field32_write(0, SPI_DEVICE_CMD_INFO_EN4B_OPCODE_FIELD, opcode);
  reg_val =
      bitfield_bit32_write(reg_val, SPI_DEVICE_CMD_INFO_EN4B_VALID_BIT, valid);
  mmio_region_write32(spi->dev.base_addr, reg_offset, reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_configure_flash_en4b_command(
    dif_spi_device_handle_t *spi, dif_toggle_t enable, uint8_t opcode) {
  return write_special_cmd_info(spi, enable, opcode,
                                SPI_DEVICE_CMD_INFO_EN4B_REG_OFFSET);
}

dif_result_t dif_spi_device_configure_flash_ex4b_command(
    dif_spi_device_handle_t *spi, dif_toggle_t enable, uint8_t opcode) {
  return write_special_cmd_info(spi, enable, opcode,
                                SPI_DEVICE_CMD_INFO_EX4B_REG_OFFSET);
}

dif_result_t dif_spi_device_configure_flash_wren_command(
    dif_spi_device_handle_t *spi, dif_toggle_t enable, uint8_t opcode) {
  return write_special_cmd_info(spi, enable, opcode,
                                SPI_DEVICE_CMD_INFO_WREN_REG_OFFSET);
}

dif_result_t dif_spi_device_configure_flash_wrdi_command(
    dif_spi_device_handle_t *spi, dif_toggle_t enable, uint8_t opcode) {
  return write_special_cmd_info(spi, enable, opcode,
                                SPI_DEVICE_CMD_INFO_WRDI_REG_OFFSET);
}

dif_result_t dif_spi_device_set_flash_address_swap(dif_spi_device_handle_t *spi,
                                                   uint32_t mask,
                                                   uint32_t replacement) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_ADDR_SWAP_MASK_REG_OFFSET,
                      mask);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_ADDR_SWAP_DATA_REG_OFFSET,
                      replacement);
  return kDifOk;
}

dif_result_t dif_spi_device_set_flash_payload_swap(dif_spi_device_handle_t *spi,
                                                   uint32_t mask,
                                                   uint32_t replacement) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr,
                      SPI_DEVICE_PAYLOAD_SWAP_MASK_REG_OFFSET, mask);
  mmio_region_write32(spi->dev.base_addr,
                      SPI_DEVICE_PAYLOAD_SWAP_DATA_REG_OFFSET, replacement);
  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_command_fifo_occupancy(
    dif_spi_device_handle_t *spi, uint8_t *occupancy) {
  if (spi == NULL || occupancy == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr,
                                        SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET);
  *occupancy = (uint8_t)bitfield_field32_read(
      reg_val, SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_DEPTH_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_address_fifo_occupancy(
    dif_spi_device_handle_t *spi, uint8_t *occupancy) {
  if (spi == NULL || occupancy == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr,
                                        SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET);
  *occupancy = (uint8_t)bitfield_field32_read(
      reg_val, SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_DEPTH_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_payload_fifo_occupancy(
    dif_spi_device_handle_t *spi, uint16_t *occupancy, uint32_t *start_offset) {
  if (spi == NULL || occupancy == NULL || start_offset == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr,
                                        SPI_DEVICE_UPLOAD_STATUS2_REG_OFFSET);
  *occupancy = (uint16_t)bitfield_field32_read(
      reg_val, SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_DEPTH_FIELD);
  *start_offset = bitfield_field32_read(
      reg_val, SPI_DEVICE_UPLOAD_STATUS2_PAYLOAD_START_IDX_FIELD);
  return kDifOk;
}

// TODO: Does the IP handle overrun / underrun correctly?
dif_result_t dif_spi_device_pop_flash_command_fifo(dif_spi_device_handle_t *spi,
                                                   uint8_t *command) {
  if (spi == NULL || command == NULL) {
    return kDifBadArg;
  }
  uint32_t upload_status = mmio_region_read32(
      spi->dev.base_addr, SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(upload_status,
                           SPI_DEVICE_UPLOAD_STATUS_CMDFIFO_NOTEMPTY_BIT)) {
    return kDifUnavailable;
  }
  uint32_t cmd_item = mmio_region_read32(spi->dev.base_addr,
                                         SPI_DEVICE_UPLOAD_CMDFIFO_REG_OFFSET);
  *command = (uint8_t)bitfield_field32_read(
      cmd_item, SPI_DEVICE_UPLOAD_CMDFIFO_DATA_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_pop_flash_address_fifo(dif_spi_device_handle_t *spi,
                                                   uint32_t *address) {
  if (spi == NULL || address == NULL) {
    return kDifBadArg;
  }
  uint32_t upload_status = mmio_region_read32(
      spi->dev.base_addr, SPI_DEVICE_UPLOAD_STATUS_REG_OFFSET);
  if (!bitfield_bit32_read(upload_status,
                           SPI_DEVICE_UPLOAD_STATUS_ADDRFIFO_NOTEMPTY_BIT)) {
    return kDifUnavailable;
  }
  *address = mmio_region_read32(spi->dev.base_addr,
                                SPI_DEVICE_UPLOAD_ADDRFIFO_REG_OFFSET);
  return kDifOk;
}

typedef struct dif_spi_device_buffer_info {
  size_t buffer_len;
  ptrdiff_t buffer_offset;
} dif_spi_device_buffer_info_t;

static dif_result_t dif_spi_device_get_flash_buffer_info(
    dif_spi_device_flash_buffer_type_t buffer_type,
    dif_spi_device_buffer_info_t *info) {
  switch (buffer_type) {
    case kDifSpiDeviceFlashBufferTypeEFlash:
      info->buffer_len = kDifSpiDeviceEFlashLen;
      info->buffer_offset = kDifSpiDeviceEFlashOffset;
      break;
    case kDifSpiDeviceFlashBufferTypeMailbox:
      info->buffer_len = kDifSpiDeviceMailboxLen;
      info->buffer_offset = kDifSpiDeviceMailboxOffset;
      break;
    case kDifSpiDeviceFlashBufferTypeSfdp:
      info->buffer_len = kDifSpiDeviceSfdpLen;
      info->buffer_offset = kDifSpiDeviceSfdpOffset;
      break;
    default:
      return kDifBadArg;
  }
  return kDifOk;
}

dif_result_t dif_spi_device_read_flash_payload_buffer(
    dif_spi_device_handle_t *spi, uint32_t offset, size_t length,
    uint8_t *buf) {
  if (spi == NULL || buf == NULL) {
    return kDifBadArg;
  }
  const dif_spi_device_buffer_info_t info = {
      .buffer_len = kDifSpiDevicePayloadLen,
      .buffer_offset = kDifSpiDevicePayloadOffset,
  };
  if (offset >= (info.buffer_offset + (ptrdiff_t)info.buffer_len) ||
      length > (info.buffer_offset + (ptrdiff_t)info.buffer_len -
                (ptrdiff_t)offset)) {
    return kDifBadArg;
  }
  ptrdiff_t offset_from_base = SPI_DEVICE_INGRESS_BUFFER_REG_OFFSET +
                               info.buffer_offset + (ptrdiff_t)offset;
  mmio_region_memcpy_from_mmio32(spi->dev.base_addr, (uint32_t)offset_from_base,
                                 buf, length);
  return kDifOk;
}

dif_result_t dif_spi_device_write_flash_buffer(
    dif_spi_device_handle_t *spi,
    dif_spi_device_flash_buffer_type_t buffer_type, uint32_t offset,
    size_t length, const uint8_t *buf) {
  if (spi == NULL || buf == NULL) {
    return kDifBadArg;
  }
  dif_spi_device_buffer_info_t info;
  dif_result_t status =
      dif_spi_device_get_flash_buffer_info(buffer_type, &info);
  if (status != kDifOk) {
    return status;
  }
  if (offset >= (info.buffer_offset + (ptrdiff_t)info.buffer_len) ||
      length > (info.buffer_offset + (ptrdiff_t)info.buffer_len -
                (ptrdiff_t)offset)) {
    return kDifBadArg;
  }
  ptrdiff_t offset_from_base = SPI_DEVICE_EGRESS_BUFFER_REG_OFFSET +
                               info.buffer_offset + (ptrdiff_t)offset;
  mmio_region_memcpy_to_mmio32(spi->dev.base_addr, (uint32_t)offset_from_base,
                               buf, length);
  return kDifOk;
}

dif_result_t dif_spi_device_get_passthrough_command_filter(
    dif_spi_device_handle_t *spi, uint8_t command, dif_toggle_t *enabled) {
  if (spi == NULL || enabled == NULL) {
    return kDifBadArg;
  }
  ptrdiff_t reg_offset =
      SPI_DEVICE_CMD_FILTER_0_REG_OFFSET + (command >> 5) * sizeof(uint32_t);
  uint32_t command_index = command & 0x1fu;
  uint32_t reg_value = mmio_region_read32(spi->dev.base_addr, reg_offset);
  bool filtered = bitfield_bit32_read(reg_value, command_index);
  if (filtered) {
    *enabled = kDifToggleEnabled;
  } else {
    *enabled = kDifToggleDisabled;
  }
  return kDifOk;
}

dif_result_t dif_spi_device_set_passthrough_command_filter(
    dif_spi_device_handle_t *spi, uint8_t command, dif_toggle_t enabled) {
  if (spi == NULL || !dif_is_valid_toggle(enabled)) {
    return kDifBadArg;
  }
  bool enable_filter = dif_toggle_to_bool(enabled);
  ptrdiff_t reg_offset =
      SPI_DEVICE_CMD_FILTER_0_REG_OFFSET + (command >> 5) * sizeof(uint32_t);
  uint32_t command_index = command & 0x1fu;
  uint32_t reg_value = mmio_region_read32(spi->dev.base_addr, reg_offset);
  reg_value = bitfield_bit32_write(reg_value, command_index, enable_filter);
  mmio_region_write32(spi->dev.base_addr, reg_offset, reg_value);
  return kDifOk;
}

dif_result_t dif_spi_device_set_all_passthrough_command_filters(
    dif_spi_device_handle_t *spi, dif_toggle_t enable) {
  if (spi == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  uint32_t reg_value = dif_toggle_to_bool(enable) ? UINT32_MAX : 0;
  for (int i = 0; i < SPI_DEVICE_CMD_FILTER_MULTIREG_COUNT; i++) {
    ptrdiff_t reg_offset =
        SPI_DEVICE_CMD_FILTER_0_REG_OFFSET + i * (ptrdiff_t)sizeof(uint32_t);
    mmio_region_write32(spi->dev.base_addr, reg_offset, reg_value);
  }
  return kDifOk;
}

dif_result_t dif_spi_device_clear_flash_busy_bit(dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr,
                                        SPI_DEVICE_FLASH_STATUS_REG_OFFSET);
  reg_val =
      bitfield_bit32_write(reg_val, SPI_DEVICE_FLASH_STATUS_WEL_BIT, false);
  reg_val =
      bitfield_bit32_write(reg_val, SPI_DEVICE_FLASH_STATUS_BUSY_BIT, false);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_FLASH_STATUS_REG_OFFSET,
                      reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_set_flash_status_registers(
    dif_spi_device_handle_t *spi, uint32_t value) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_FLASH_STATUS_REG_OFFSET,
                      value);
  return kDifOk;
}

dif_result_t dif_spi_device_get_flash_status_registers(
    dif_spi_device_handle_t *spi, uint32_t *value) {
  if (spi == NULL || value == NULL) {
    return kDifBadArg;
  }
  *value = mmio_region_read32(spi->dev.base_addr,
                              SPI_DEVICE_FLASH_STATUS_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_spi_device_get_tpm_capabilities(
    dif_spi_device_handle_t *spi, dif_spi_device_tpm_caps_t *caps) {
  if (spi == NULL || caps == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_TPM_CAP_REG_OFFSET);
  caps->revision =
      (uint8_t)bitfield_field32_read(reg_val, SPI_DEVICE_TPM_CAP_REV_FIELD);
  caps->multi_locality =
      bitfield_bit32_read(reg_val, SPI_DEVICE_TPM_CAP_LOCALITY_BIT);
  caps->max_write_size = (uint8_t)bitfield_field32_read(
      reg_val, SPI_DEVICE_TPM_CAP_MAX_WR_SIZE_FIELD);
  caps->max_read_size = (uint8_t)bitfield_field32_read(
      reg_val, SPI_DEVICE_TPM_CAP_MAX_RD_SIZE_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_configure(dif_spi_device_handle_t *spi,
                                          dif_toggle_t enable,
                                          dif_spi_device_tpm_config_t config) {
  if (spi == NULL || !dif_is_valid_toggle(enable)) {
    return kDifBadArg;
  }
  bool tpm_en = dif_toggle_to_bool(enable);
  uint32_t reg_val = bitfield_bit32_write(0, SPI_DEVICE_TPM_CFG_EN_BIT, tpm_en);
  if (tpm_en) {
    bool use_crb;
    switch (config.interface) {
      case kDifSpiDeviceTpmInterfaceFifo:
        use_crb = false;
        break;
      case kDifSpiDeviceTpmInterfaceCrb:
        use_crb = true;
        break;
      default:
        return kDifBadArg;
    }
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_TPM_CFG_TPM_MODE_BIT, use_crb);
    reg_val = bitfield_bit32_write(reg_val, SPI_DEVICE_TPM_CFG_HW_REG_DIS_BIT,
                                   config.disable_return_by_hardware);
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_TPM_CFG_TPM_REG_CHK_DIS_BIT,
                             config.disable_address_prefix_check);
    reg_val =
        bitfield_bit32_write(reg_val, SPI_DEVICE_TPM_CFG_INVALID_LOCALITY_BIT,
                             config.disable_locality_check);
  }
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_TPM_CFG_REG_OFFSET,
                      reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_get_data_status(
    dif_spi_device_handle_t *spi, dif_spi_device_tpm_data_status_t *status) {
  if (spi == NULL || status == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_TPM_STATUS_REG_OFFSET);
  status->cmd_addr_valid =
      bitfield_bit32_read(reg_val, SPI_DEVICE_TPM_STATUS_CMDADDR_NOTEMPTY_BIT);
  status->wrfifo_acquired =
      bitfield_bit32_read(reg_val, SPI_DEVICE_TPM_STATUS_WRFIFO_PENDING_BIT);
  status->rdfifo_aborted =
      bitfield_bit32_read(reg_val, SPI_DEVICE_TPM_STATUS_RDFIFO_ABORTED_BIT);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_set_access_reg(dif_spi_device_handle_t *spi,
                                               uint8_t locality,
                                               uint8_t value) {
  if (spi == NULL || locality >= SPI_DEVICE_PARAM_NUM_LOCALITY) {
    return kDifBadArg;
  }
  // There is one 8-bit TPM_ACCESS register per locality, but bus accesses are
  // 32 bits.
  ptrdiff_t reg_offset = SPI_DEVICE_TPM_ACCESS_0_REG_OFFSET + (locality & 0xfc);
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr, reg_offset);
  switch (locality & 0x03) {
    case 0:
      reg_val = bitfield_field32_write(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_0_FIELD, value);
      break;
    case 1:
      reg_val = bitfield_field32_write(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_1_FIELD, value);
      break;
    case 2:
      reg_val = bitfield_field32_write(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_2_FIELD, value);
      break;
    case 3:
      reg_val = bitfield_field32_write(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_3_FIELD, value);
      break;
    default:
      break;
  }
  mmio_region_write32(spi->dev.base_addr, reg_offset, reg_val);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_get_access_reg(dif_spi_device_handle_t *spi,
                                               uint8_t locality,
                                               uint8_t *value) {
  if (spi == NULL || locality >= SPI_DEVICE_PARAM_NUM_LOCALITY ||
      value == NULL) {
    return kDifBadArg;
  }
  // There is one 8-bit TPM_ACCESS register per locality, but bus accesses are
  // 32 bits.
  ptrdiff_t reg_offset = SPI_DEVICE_TPM_ACCESS_0_REG_OFFSET + (locality & 0xfc);
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr, reg_offset);
  switch (locality & 0x03) {
    case 0:
      *value = (uint8_t)bitfield_field32_read(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_0_FIELD);
      break;
    case 1:
      *value = (uint8_t)bitfield_field32_read(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_1_FIELD);
      break;
    case 2:
      *value = (uint8_t)bitfield_field32_read(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_2_FIELD);
      break;
    case 3:
      *value = (uint8_t)bitfield_field32_read(
          reg_val, SPI_DEVICE_TPM_ACCESS_0_ACCESS_3_FIELD);
      break;
    default:
      break;
  }
  return kDifOk;
}

/**
 * Write a TPM register used with the return-by-hardware logic.
 *
 * @param spi A handle to a spi device.
 * @param value The value to write.
 * @param reg_offset The offset of the related CSR from the spi device's base.
 * @return The result of the operation.
 */
static dif_result_t tpm_reg_write32(dif_spi_device_handle_t *spi,
                                    uint32_t value, ptrdiff_t reg_offset) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(spi->dev.base_addr, reg_offset, value);
  return kDifOk;
}

/**
 * Read from a TPM register used with the return-by-hardware logic.
 *
 * @param spi A handle to a spi device.
 * @param value The value read.
 * @param reg_offset The offset of the related CSR from the spi device's base.
 * @return The result of the operation.
 */
static dif_result_t tpm_reg_read32(dif_spi_device_handle_t *spi,
                                   uint32_t *value, ptrdiff_t reg_offset) {
  if (spi == NULL || value == NULL) {
    return kDifBadArg;
  }
  *value = mmio_region_read32(spi->dev.base_addr, reg_offset);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_set_sts_reg(dif_spi_device_handle_t *spi,
                                            uint32_t value) {
  return tpm_reg_write32(spi, value, SPI_DEVICE_TPM_STS_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_get_sts_reg(dif_spi_device_handle_t *spi,
                                            uint32_t *value) {
  return tpm_reg_read32(spi, value, SPI_DEVICE_TPM_STS_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_set_intf_capability_reg(
    dif_spi_device_handle_t *spi, uint32_t value) {
  return tpm_reg_write32(spi, value, SPI_DEVICE_TPM_INTF_CAPABILITY_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_get_intf_capability_reg(
    dif_spi_device_handle_t *spi, uint32_t *value) {
  return tpm_reg_read32(spi, value, SPI_DEVICE_TPM_INTF_CAPABILITY_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_set_int_enable_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t value) {
  return tpm_reg_write32(spi, value, SPI_DEVICE_TPM_INT_ENABLE_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_get_int_enable_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t *value) {
  return tpm_reg_read32(spi, value, SPI_DEVICE_TPM_INT_ENABLE_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_set_int_vector_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t value) {
  return tpm_reg_write32(spi, value, SPI_DEVICE_TPM_INT_VECTOR_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_get_int_vector_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t *value) {
  return tpm_reg_read32(spi, value, SPI_DEVICE_TPM_INT_VECTOR_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_set_int_status_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t value) {
  return tpm_reg_write32(spi, value, SPI_DEVICE_TPM_INT_STATUS_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_get_int_status_reg(dif_spi_device_handle_t *spi,
                                                   uint32_t *value) {
  return tpm_reg_read32(spi, value, SPI_DEVICE_TPM_INT_STATUS_REG_OFFSET);
}

dif_result_t dif_spi_device_tpm_set_id(dif_spi_device_handle_t *spi,
                                       dif_spi_device_tpm_id_t id) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val;
  reg_val =
      bitfield_field32_write(0, SPI_DEVICE_TPM_DID_VID_VID_FIELD, id.vendor_id);
  reg_val = bitfield_field32_write(reg_val, SPI_DEVICE_TPM_DID_VID_DID_FIELD,
                                   id.device_id);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_TPM_DID_VID_REG_OFFSET,
                      reg_val);
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_TPM_RID_REG_OFFSET,
                      id.revision);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_get_id(dif_spi_device_handle_t *spi,
                                       dif_spi_device_tpm_id_t *value) {
  if (spi == NULL || value == NULL) {
    return kDifBadArg;
  }
  uint32_t did_vid =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_TPM_DID_VID_REG_OFFSET);
  uint32_t rid =
      mmio_region_read32(spi->dev.base_addr, SPI_DEVICE_TPM_RID_REG_OFFSET);
  value->vendor_id = (uint16_t)bitfield_field32_read(
      did_vid, SPI_DEVICE_TPM_DID_VID_VID_FIELD);
  value->device_id = (uint16_t)bitfield_field32_read(
      did_vid, SPI_DEVICE_TPM_DID_VID_DID_FIELD);
  value->revision =
      (uint8_t)bitfield_field32_read(rid, SPI_DEVICE_TPM_RID_RID_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_get_command(dif_spi_device_handle_t *spi,
                                            uint8_t *command,
                                            uint32_t *address) {
  if (spi == NULL || command == NULL || address == NULL) {
    return kDifBadArg;
  }
  uint32_t reg_val = mmio_region_read32(spi->dev.base_addr,
                                        SPI_DEVICE_TPM_CMD_ADDR_REG_OFFSET);
  *command = (uint8_t)bitfield_field32_read(reg_val,
                                            SPI_DEVICE_TPM_CMD_ADDR_CMD_FIELD);
  *address = bitfield_field32_read(reg_val, SPI_DEVICE_TPM_CMD_ADDR_ADDR_FIELD);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_write_data(dif_spi_device_handle_t *spi,
                                           size_t length, uint8_t *buf) {
  if (spi == NULL || buf == NULL) {
    return kDifBadArg;
  }
  dif_spi_device_tpm_data_status_t status;
  dif_result_t result = dif_spi_device_tpm_get_data_status(spi, &status);
  uint8_t offset = length & 0x3;  // lower two bits of length
  uint32_t rdfifo_wdata;

  DIF_RETURN_IF_ERROR(result);

  // TODO: Ensure the received length is greater than FIFO SIZE
  if (DIF_SPI_DEVICE_TPM_FIFO_DEPTH * sizeof(uint32_t) < length) {
    return kDifOutOfRange;
  }
  for (int i = 0; i < length; i += 4) {
    if (i + 4 > length) {
      // Send partial
      rdfifo_wdata = 0;
      for (int j = 0; j <= offset; j++) {
        rdfifo_wdata |= (uint32_t)(buf[i + j]) << (8 * j);
      }
    } else {
      // Type casting to uint32_t then fetch
      rdfifo_wdata = *((uint32_t *)buf + (i >> 2));
    }
    mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_TPM_READ_FIFO_REG_OFFSET,
                        rdfifo_wdata);
  }
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_read_data(dif_spi_device_handle_t *spi,
                                          size_t length, uint8_t *buf) {
  if (spi == NULL || buf == NULL) {
    return kDifBadArg;
  }
  const uint32_t kOffset = 0;
  const dif_spi_device_buffer_info_t kInfo = {
      .buffer_len = kDifSpiDeviceTpmWriteFifoLen,
      .buffer_offset = kDifSpiDeviceTpmWriteFifoOffset,
  };
  if (kOffset >= (kInfo.buffer_offset + (ptrdiff_t)kInfo.buffer_len) ||
      length > (kInfo.buffer_offset + (ptrdiff_t)kInfo.buffer_len -
                (ptrdiff_t)kOffset)) {
    return kDifBadArg;
  }
  ptrdiff_t offset_from_base = SPI_DEVICE_INGRESS_BUFFER_REG_OFFSET +
                               kInfo.buffer_offset + (ptrdiff_t)kOffset;
  mmio_region_memcpy_from_mmio32(spi->dev.base_addr, (uint32_t)offset_from_base,
                                 buf, length);
  return kDifOk;
}

dif_result_t dif_spi_device_tpm_free_write_fifo(dif_spi_device_handle_t *spi) {
  if (spi == NULL) {
    return kDifBadArg;
  }
  // TPM_STATUS.wrfifo_pending is the only writeable CSR, and it's RW0C.
  mmio_region_write32(spi->dev.base_addr, SPI_DEVICE_TPM_STATUS_REG_OFFSET, 0);
  return kDifOk;
}
