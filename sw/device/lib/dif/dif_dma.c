// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_dma.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "dma_regs.h"  // Generated.

static_assert(kDifDmaOpentitanInternalBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_OT_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCControlRegisterBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SOC_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCSystemBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SYS_ADDR_,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaOpentitanExternalFlash ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_FLASH_ADDR,
              "Address Space ID mismatches with value defined in HW");

dif_result_t dif_dma_configure(const dif_dma_t *dma,
                               dif_dma_transaction_t transaction) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(dma->base_addr, DMA_SOURCE_ADDRESS_LO_REG_OFFSET,
                      transaction.source.address & UINT32_MAX);
  mmio_region_write32(dma->base_addr, DMA_SOURCE_ADDRESS_HI_REG_OFFSET,
                      transaction.source.address >> (sizeof(uint32_t) * 8));

  mmio_region_write32(dma->base_addr, DMA_DESTINATION_ADDRESS_LO_REG_OFFSET,
                      transaction.destination.address & UINT32_MAX);
  mmio_region_write32(
      dma->base_addr, DMA_DESTINATION_ADDRESS_HI_REG_OFFSET,
      transaction.destination.address >> (sizeof(uint32_t) * 8));

  uint32_t reg = 0;
  reg = bitfield_field32_write(reg, DMA_ADDRESS_SPACE_ID_SOURCE_ASID_FIELD,
                               transaction.source.asid);
  reg = bitfield_field32_write(reg, DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_FIELD,
                               transaction.destination.asid);
  mmio_region_write32(dma->base_addr, DMA_ADDRESS_SPACE_ID_REG_OFFSET, reg);

  mmio_region_write32(dma->base_addr, DMA_TOTAL_DATA_SIZE_REG_OFFSET,
                      transaction.size);
  mmio_region_write32(dma->base_addr, DMA_TRANSFER_WIDTH_REG_OFFSET,
                      transaction.width);

  return kDifOk;
}

dif_result_t dif_dma_handshake_enable(const dif_dma_t *dma,
                                      dif_dma_handshake_t handshake) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(dma->base_addr, DMA_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT,
                             true);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_FIFO_AUTO_INCREMENT_ENABLE_BIT,
                             handshake.fifo_auto_increment);
  reg = bitfield_bit32_write(
      reg, DMA_CONTROL_MEMORY_BUFFER_AUTO_INCREMENT_ENABLE_BIT,
      handshake.memory_auto_increment);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_DATA_DIRECTION_BIT,
                             handshake.direction_from_mem_to_fifo);
  mmio_region_write32(dma->base_addr, DMA_CONTROL_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_dma_start(const dif_dma_t *dma,
                           dif_dma_transaction_opcode_t opcode) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(dma->base_addr, DMA_CONTROL_REG_OFFSET);
  reg = bitfield_field32_write(reg, DMA_CONTROL_OPCODE_FIELD, opcode);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_GO_BIT, 1);
  mmio_region_write32(dma->base_addr, DMA_CONTROL_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_dma_abort(const dif_dma_t *dma) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(dma->base_addr, DMA_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_ABORT_BIT, 1);
  mmio_region_write32(dma->base_addr, DMA_CONTROL_REG_OFFSET, reg);
  return kDifOk;
}

dif_result_t dif_dma_is_locked(const dif_dma_t *dma, bool *is_locked) {
  return kDifUnavailable;
}
