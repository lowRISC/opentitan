// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"

#include "sw/device/lib/base/bitfield.h"
#include "otbn_regs.h"  // Generated.

/**
 * WLEN: width of wide instructions in OTBN, in bits.
 */
const int kDifOtbnWlen = 256;

dif_otbn_result_t dif_otbn_init(const dif_otbn_config_t *config,
                                dif_otbn_t *otbn) {
  if (config == NULL || otbn == NULL) {
    return kDifOtbnBadArg;
  }

  otbn->base_addr = config->base_addr;
  dif_otbn_reset(otbn);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_reset(const dif_otbn_t *otbn) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  mmio_region_write32(otbn->base_addr, OTBN_INTR_ENABLE_REG_OFFSET, 0);

  // Clear all pending interrupts.
  mmio_region_write32(otbn->base_addr, OTBN_INTR_STATE_REG_OFFSET, 0xFFFFFFFF);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_start(const dif_otbn_t *otbn) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  mmio_region_write_only_set_bit32(otbn->base_addr, OTBN_CMD_REG_OFFSET,
                                   OTBN_CMD_START);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_is_busy(const dif_otbn_t *otbn, bool *busy) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  uint32_t status = mmio_region_read32(otbn->base_addr, OTBN_STATUS_REG_OFFSET);
  *busy = bitfield_get_field32(
    status,
    (bitfield_field32_t){
        .mask = 1, .index = OTBN_STATUS_BUSY,
    });

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_imem_write(const dif_otbn_t *otbn, uint32_t offset,
                                      const void *src, size_t len) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }
  if (len % 4 != 0) {
    // Only word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset % 4 != 0) {
    // Only word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset + len > OTBN_IMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset,
                               src, len);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_imem_read(const dif_otbn_t *otbn, uint32_t offset,
                                     void *dest, size_t len) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  if (len % 4 != 0) {
    // Only 32b word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset % 4 != 0) {
    // Only 32b word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset + len > OTBN_DMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_from_mmio32(otbn->base_addr, OTBN_IMEM_REG_OFFSET + offset,
                                 dest, len);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn, uint32_t offset,
                                      const void *src, size_t len) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  if (len % (kDifOtbnWlen / 8) != 0) {
    // Only WLEN word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset % (kDifOtbnWlen / 8) != 0) {
    // Only WLEN word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset + len > OTBN_DMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_to_mmio32(otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset,
                               src, len);

  return kDifOtbnOk;
}

dif_otbn_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn, uint32_t offset,
                                     void *dest, size_t len) {
  if (otbn == NULL) {
    return kDifOtbnBadArg;
  }

  if (len % (kDifOtbnWlen / 8) != 0) {
    // Only WLEN word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset % (kDifOtbnWlen / 8) != 0) {
    // Only WLEN word access is allowed.
    return kDifOtbnBadArg;
  }
  if (offset + len > OTBN_DMEM_SIZE_BYTES) {
    return kDifOtbnBadArg;
  }

  mmio_region_memcpy_from_mmio32(otbn->base_addr, OTBN_DMEM_REG_OFFSET + offset,
                                 dest, len);

  return kDifOtbnOk;
}
