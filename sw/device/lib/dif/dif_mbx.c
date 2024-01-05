// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_mbx.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "mbx_regs.h"  // Generated.

dif_result_t dif_mbx_range_set(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t config) {
  if (mbx == NULL) {
    return kDifBadArg;
  }
  // Note: the limit addresses are _inclusive_, specifying the start address of
  // the final valid DWORD.
  if (config.imbx_base_addr > config.imbx_limit_addr) {
    return kDifBadArg;
  }
  if (config.ombx_base_addr > config.ombx_limit_addr) {
    return kDifBadArg;
  }
  // Check that the inbound mailbox and outbound mailbox memory ranges do not
  // collide with each other.
  if ((config.imbx_base_addr <= config.ombx_limit_addr) &&
      (config.ombx_base_addr <= config.imbx_limit_addr)) {
    return kDifBadArg;
  }

  mmio_region_write32(mbx->base_addr, MBX_INBOUND_BASE_ADDRESS_REG_OFFSET,
                      config.imbx_base_addr);
  mmio_region_write32(mbx->base_addr, MBX_INBOUND_LIMIT_ADDRESS_REG_OFFSET,
                      config.imbx_limit_addr);
  mmio_region_write32(mbx->base_addr, MBX_OUTBOUND_BASE_ADDRESS_REG_OFFSET,
                      config.ombx_base_addr);
  mmio_region_write32(mbx->base_addr, MBX_OUTBOUND_LIMIT_ADDRESS_REG_OFFSET,
                      config.ombx_limit_addr);
  // Indicate the range configuration to be valid.
  mmio_region_write32(mbx->base_addr, MBX_ADDRESS_RANGE_VALID_REG_OFFSET, 1);

  return kDifOk;
}

dif_result_t dif_mbx_range_get(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t *config) {
  if (mbx == NULL || config == NULL) {
    return kDifBadArg;
  }

  config->imbx_base_addr =
      mmio_region_read32(mbx->base_addr, MBX_INBOUND_BASE_ADDRESS_REG_OFFSET);
  config->imbx_limit_addr =
      mmio_region_read32(mbx->base_addr, MBX_INBOUND_LIMIT_ADDRESS_REG_OFFSET);
  config->ombx_base_addr =
      mmio_region_read32(mbx->base_addr, MBX_OUTBOUND_BASE_ADDRESS_REG_OFFSET);
  config->ombx_limit_addr =
      mmio_region_read32(mbx->base_addr, MBX_OUTBOUND_LIMIT_ADDRESS_REG_OFFSET);
  return kDifOk;
}

dif_result_t dif_mbx_is_busy(const dif_mbx_t *mbx, bool *is_busy) {
  if (mbx == NULL || is_busy == NULL) {
    return kDifBadArg;
  }

  *is_busy = (bitfield_bit32_read(
                  mmio_region_read32(mbx->base_addr, MBX_STATUS_REG_OFFSET),
                  MBX_STATUS_BUSY_BIT) == 1);
  return kDifOk;
}

dif_result_t dif_mbx_process_request(const dif_mbx_t *mbx,
                                     dif_mbx_transaction_t *request) {
  if (mbx == NULL || request == NULL || request->data_dwords == NULL) {
    return kDifBadArg;
  }

  uint32_t curr_ptr =
      mmio_region_read32(mbx->base_addr, MBX_INBOUND_BASE_ADDRESS_REG_OFFSET);
  uint32_t imbx_wr_ptr =
      mmio_region_read32(mbx->base_addr, MBX_INBOUND_WRITE_PTR_REG_OFFSET);

  // Read from base until the write pointer.
  request->nr_dwords = 0;
  while (curr_ptr < imbx_wr_ptr) {
    request->data_dwords[request->nr_dwords++] = abs_mmio_read32(curr_ptr);
    curr_ptr += sizeof(uint32_t);
  }
  return kDifOk;
}

dif_result_t dif_mbx_generate_response(const dif_mbx_t *mbx,
                                       const dif_mbx_transaction_t response) {
  uint32_t curr_ptr;

  if (mbx == NULL || response.data_dwords == NULL ||
      response.nr_dwords > DOE_MAILBOX_MAX_OBJECT_SIZE) {
    return kDifBadArg;
  }

  curr_ptr =
      mmio_region_read32(mbx->base_addr, MBX_OUTBOUND_READ_PTR_REG_OFFSET);
  for (uint32_t i = 0; i < response.nr_dwords; ++i) {
    abs_mmio_write32(curr_ptr, response.data_dwords[i]);
    curr_ptr += sizeof(uint32_t);
  }

  mmio_region_write32(mbx->base_addr, MBX_OUTBOUND_OBJECT_SIZE_REG_OFFSET,
                      response.nr_dwords);

  return kDifOk;
}
