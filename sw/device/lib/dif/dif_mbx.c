// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_mbx.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "mbx_regs.h"  // Generated.

dif_result_t dif_mbx_range_set(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t config) {
  if (mbx == NULL) {
    return kDifBadArg;
  }
  if (config.imbx_base_addr >= config.imbx_limit_addr) {
    return kDifBadArg;
  }
  if (config.ombx_base_addr >= config.ombx_limit_addr) {
    return kDifBadArg;
  }
  // Check that the inbound mailbox and outbound mailbox memory ranges collide
  // with each other.
  if ((config.imbx_base_addr < config.ombx_limit_addr) &&
      (config.ombx_base_addr < config.imbx_limit_addr)) {
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
