// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_device.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_device_regs.h"  // Generated.

enum {
  /**
   * Base address of the spi_device registers.
   */
  kBase = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
};

void spi_device_init(void) {
  // CPOL = 0, CPHA = 0, MSb-first TX and RX, 3-byte addressing.
  uint32_t reg = bitfield_bit32_write(0, SPI_DEVICE_CFG_CPOL_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_CPHA_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_TX_ORDER_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_RX_ORDER_BIT, false);
  reg = bitfield_field32_write(reg, SPI_DEVICE_CFG_TIMER_V_FIELD, 0x7f);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_ADDR_4B_EN_BIT, false);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CFG_MAILBOX_EN_BIT, false);
  abs_mmio_write32(kBase + SPI_DEVICE_CFG_REG_OFFSET, reg);

  // JEDEC manufacturer and device ID.
  // spi_device sends these in the following order: continuation codes,
  // manufacturer ID, LSB of device ID, and MSB of device ID (density).
  reg = bitfield_field32_write(0, SPI_DEVICE_JEDEC_CC_CC_FIELD,
                               kSpiDeviceJedecContCode);
  reg = bitfield_field32_write(reg, SPI_DEVICE_JEDEC_CC_NUM_CC_FIELD,
                               kSpiDeviceJedecContCodeCount);
  abs_mmio_write32(kBase + SPI_DEVICE_JEDEC_CC_REG_OFFSET, reg);
  // TODO(#11605): Use the HW revision register when available.
  reg = bitfield_field32_write(0, SPI_DEVICE_DEV_ID_CHIP_REV_FIELD, 0);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_DEV_ID_ROM_BOOTSTRAP_BIT, true);
  reg = bitfield_field32_write(reg, SPI_DEVICE_DEV_ID_CHIP_GEN_FIELD, 0);
  reg = bitfield_field32_write(reg, SPI_DEVICE_DEV_ID_DENSITY_FIELD,
                               kSpiDeviceJedecDensity);
  reg = bitfield_field32_write(reg, SPI_DEVICE_JEDEC_ID_MF_FIELD,
                               kSpiDeviceJedecManufId);
  abs_mmio_write32(kBase + SPI_DEVICE_JEDEC_ID_REG_OFFSET, reg);

  // Configure READ_JEDEC_ID command (CMD_INFO_3).
  reg = bitfield_field32_write(0, SPI_DEVICE_CMD_INFO_3_OPCODE_3_FIELD,
                               kSpiDeviceCmdReadJedecId);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CMD_INFO_3_VALID_3_BIT, true);
  abs_mmio_write32(kBase + SPI_DEVICE_CMD_INFO_3_REG_OFFSET, reg);

  // Reset status register
  abs_mmio_write32(kBase + SPI_DEVICE_FLASH_STATUS_REG_OFFSET, 0);

  // Switch to flash mode. Both clocks (SRAM and SPI) must be disabled prior to
  // mode change for proper SRAM operation.
  reg = abs_mmio_read32(kBase + SPI_DEVICE_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CONTROL_SRAM_CLK_EN_BIT, false);
  abs_mmio_write32(kBase + SPI_DEVICE_CONTROL_REG_OFFSET, reg);
  reg = bitfield_field32_write(0, SPI_DEVICE_CONTROL_MODE_FIELD,
                               SPI_DEVICE_CONTROL_MODE_VALUE_FLASHMODE);
  abs_mmio_write32(kBase + SPI_DEVICE_CONTROL_REG_OFFSET, reg);
  reg = bitfield_bit32_write(reg, SPI_DEVICE_CONTROL_SRAM_CLK_EN_BIT, true);
  abs_mmio_write32(kBase + SPI_DEVICE_CONTROL_REG_OFFSET, reg);
}
