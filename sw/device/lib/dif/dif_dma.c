// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_dma.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

static_assert(kDifDmaOpentitanInternalBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_OT_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCControlRegisterBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SOC_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCSystemBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SYS_ADDR_,
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

  mmio_region_write32(dma->base_addr, DMA_CHUNK_DATA_SIZE_REG_OFFSET,
                      transaction.chunk_size);
  mmio_region_write32(dma->base_addr, DMA_TOTAL_DATA_SIZE_REG_OFFSET,
                      transaction.total_size);
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

dif_result_t dif_dma_handshake_disable(const dif_dma_t *dma) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  uint32_t reg = mmio_region_read32(dma->base_addr, DMA_CONTROL_REG_OFFSET);
  reg = bitfield_bit32_write(reg, DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT,
                             false);
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
  reg = bitfield_bit32_write(reg, DMA_CONTROL_INITIAL_TRANSFER_BIT, 1);
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

dif_result_t dif_dma_memory_range_set(const dif_dma_t *dma, uint32_t address,
                                      size_t size) {
  if (dma == NULL || size == 0) {
    return kDifBadArg;
  }

  mmio_region_write32(dma->base_addr, DMA_ENABLED_MEMORY_RANGE_BASE_REG_OFFSET,
                      address);
  // The limit address is inclusive so we subtract one.
  uint32_t end_addr = address + size - 1;
  mmio_region_write32(dma->base_addr, DMA_ENABLED_MEMORY_RANGE_LIMIT_REG_OFFSET,
                      end_addr);
  // Indicate the range to be valid
  mmio_region_write32(dma->base_addr, DMA_RANGE_VALID_REG_OFFSET, 1);

  return kDifOk;
}

dif_result_t dif_dma_memory_range_get(const dif_dma_t *dma, uint32_t *address,
                                      size_t *size) {
  if (dma == NULL || size == NULL || address == NULL) {
    return kDifBadArg;
  }

  *address = mmio_region_read32(dma->base_addr,
                                DMA_ENABLED_MEMORY_RANGE_BASE_REG_OFFSET);

  // The limit address is inclusive so we add one.
  *size = mmio_region_read32(dma->base_addr,
                             DMA_ENABLED_MEMORY_RANGE_LIMIT_REG_OFFSET) -
          *address + 1;

  return kDifOk;
}

dif_result_t dif_dma_memory_range_lock(const dif_dma_t *dma) {
  if (dma == NULL) {
    return kDifBadArg;
  }

  mmio_region_write32(dma->base_addr, DMA_RANGE_REGWEN_REG_OFFSET,
                      kMultiBitBool4False);
  return kDifOk;
}

dif_result_t dif_dma_is_memory_range_locked(const dif_dma_t *dma,
                                            bool *is_locked) {
  if (dma == NULL || is_locked == NULL) {
    return kDifBadArg;
  }

  *is_locked = kMultiBitBool4False ==
               mmio_region_read32(dma->base_addr, DMA_RANGE_REGWEN_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_dma_is_memory_range_valid(const dif_dma_t *dma,
                                           bool *is_valid) {
  if (dma == NULL || is_valid == NULL) {
    return kDifBadArg;
  }

  *is_valid = mmio_region_read32(dma->base_addr, DMA_RANGE_VALID_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_dma_irq_thresholds_set(const dif_dma_t *dma,
                                        uint64_t almost_limit, uint64_t limit) {
  if (dma == NULL || almost_limit > limit) {
    return kDifBadArg;
  }

  mmio_region_write32(dma->base_addr,
                      DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_LO_REG_OFFSET,
                      almost_limit & UINT32_MAX);
  mmio_region_write32(dma->base_addr,
                      DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_HI_REG_OFFSET,
                      almost_limit >> (sizeof(uint32_t) * 8));

  mmio_region_write32(dma->base_addr,
                      DMA_DESTINATION_ADDRESS_LIMIT_LO_REG_OFFSET,
                      limit & UINT32_MAX);
  mmio_region_write32(dma->base_addr,
                      DMA_DESTINATION_ADDRESS_LIMIT_HI_REG_OFFSET,
                      limit >> (sizeof(uint32_t) * 8));

  return kDifOk;
}

dif_result_t dif_dma_irq_thresholds_get(const dif_dma_t *dma,
                                        uint64_t *almost_limit,
                                        uint64_t *limit) {
  if (dma == NULL || almost_limit == NULL || limit == NULL) {
    return kDifBadArg;
  }

  uint64_t val_lo = mmio_region_read32(
      dma->base_addr, DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_LO_REG_OFFSET);
  uint64_t val_hi = mmio_region_read32(
      dma->base_addr, DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_HI_REG_OFFSET);
  *almost_limit = val_lo | (val_hi << (sizeof(uint32_t) * 8));

  val_lo = mmio_region_read32(dma->base_addr,
                              DMA_DESTINATION_ADDRESS_LIMIT_LO_REG_OFFSET);
  val_hi = mmio_region_read32(dma->base_addr,
                              DMA_DESTINATION_ADDRESS_LIMIT_HI_REG_OFFSET);
  *limit = val_lo | (val_hi << (sizeof(uint32_t) * 8));

  return kDifOk;
}

dif_result_t dif_dma_status_get(const dif_dma_t *dma,
                                dif_dma_status_t *status) {
  if (dma == NULL || status == NULL) {
    return kDifBadArg;
  }
  *status = mmio_region_read32(dma->base_addr, DMA_STATUS_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_dma_status_write(const dif_dma_t *dma,
                                  dif_dma_status_t status) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr, DMA_STATUS_REG_OFFSET, status);

  return kDifOk;
}

dif_result_t dif_dma_status_clear(const dif_dma_t *dma) {
  return dif_dma_status_write(dma, kDifDmaStatusDone | kDifDmaStatusAborted |
                                       kDifDmaStatusError | kDifDmaStatusError);
}

dif_result_t dif_dma_status_poll(const dif_dma_t *dma,
                                 dif_dma_status_code_t flag) {
  while (true) {
    dif_dma_status_t status;
    DIF_RETURN_IF_ERROR(dif_dma_status_get(dma, &status));

    if (status & flag) {
      break;
    }
    if (status & kDifDmaStatusError) {
      return kDifError;
    }
  }
  return kDifOk;
}

dif_result_t dif_dma_error_code_get(const dif_dma_t *dma,
                                    dif_dma_error_code_t *error) {
  if (dma == NULL || error == NULL) {
    return kDifBadArg;
  }
  *error = mmio_region_read32(dma->base_addr, DMA_ERROR_CODE_REG_OFFSET);

  return kDifOk;
}

dif_result_t dif_dma_sha2_digest_get(const dif_dma_t *dma,
                                     dif_dma_transaction_opcode_t opcode,
                                     uint32_t digest[]) {
  if (dma == NULL || digest == NULL) {
    return kDifBadArg;
  }

  uint32_t regs_num;
  switch (opcode) {
    case kDifDmaSha256Opcode:
      regs_num = 8;
      break;
    case kDifDmaSha384Opcode:
      regs_num = 12;
      break;
    case kDifDmaSha512Opcode:
      regs_num = 16;
      break;
    default:
      regs_num = 0;
  }

  for (int i = 0; i < regs_num; ++i) {
    ptrdiff_t offset = DMA_SHA2_DIGEST_0_REG_OFFSET +
                       (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t);

    digest[i] = mmio_region_read32(dma->base_addr, offset);
  }
  return kDifOk;
}

dif_result_t dif_dma_handshake_irq_enable(const dif_dma_t *dma,
                                          uint32_t enable_state) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr, DMA_HANDSHAKE_INTERRUPT_ENABLE_REG_OFFSET,
                      enable_state);
  return kDifOk;
}

dif_result_t dif_dma_handshake_clear_irq(const dif_dma_t *dma,
                                         uint32_t clear_state) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr, DMA_CLEAR_INT_SRC_REG_OFFSET,
                      clear_state);

  return kDifOk;
}

dif_result_t dif_dma_handshake_clear_irq_bus(const dif_dma_t *dma,
                                             uint32_t clear_irq_bus) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr, DMA_CLEAR_INT_BUS_REG_OFFSET,
                      clear_irq_bus);

  return kDifOk;
}

dif_result_t dif_dma_int_src_addr(const dif_dma_t *dma, dif_dma_int_idx_t idx,
                                  uint32_t int_src_addr) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr,
                      DMA_INT_SOURCE_ADDR_0_REG_OFFSET + (ptrdiff_t)idx,
                      int_src_addr);
  return kDifOk;
}

dif_result_t dif_dma_int_write_value(const dif_dma_t *dma,
                                     dif_dma_int_idx_t idx,
                                     uint32_t int_src_value) {
  if (dma == NULL) {
    return kDifBadArg;
  }
  mmio_region_write32(dma->base_addr,
                      DMA_INT_SOURCE_WR_VAL_0_REG_OFFSET + (ptrdiff_t)idx,
                      int_src_value);
  return kDifOk;
}
