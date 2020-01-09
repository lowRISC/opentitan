// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"

// |extern| declarations to give the inline functions in the
// corresponding header a link location.
extern uint8_t mmio_region_read8(mmio_region_t base, ptrdiff_t offset);
extern uint16_t mmio_region_read16(mmio_region_t base, ptrdiff_t offset);
extern uint32_t mmio_region_read32(mmio_region_t base, ptrdiff_t offset);
extern void mmio_region_write8(mmio_region_t base, ptrdiff_t offset,
                               uint8_t value);
extern void mmio_region_write16(mmio_region_t base, ptrdiff_t offset,
                                uint16_t value);
extern void mmio_region_write32(mmio_region_t base, ptrdiff_t offset,
                                uint32_t value);
extern uint32_t mmio_region_read_mask32(mmio_region_t base, ptrdiff_t offset,
                                        uint32_t mask, uint32_t mask_index);
extern bool mmio_region_get_bit32(mmio_region_t base, ptrdiff_t offset,
                                  uint32_t bit_index);
extern void mmio_region_nonatomic_clear_mask32(mmio_region_t base,
                                               ptrdiff_t offset, uint32_t mask,
                                               uint32_t mask_index);
extern void mmio_region_nonatomic_set_mask32(mmio_region_t base,
                                             ptrdiff_t offset, uint32_t mask,
                                             uint32_t mask_index);
extern void mmio_region_nonatomic_clear_bit32(mmio_region_t base,
                                              ptrdiff_t offset,
                                              uint32_t bit_index);
extern void mmio_region_nonatomic_set_bit32(mmio_region_t base,
                                            ptrdiff_t offset,
                                            uint32_t bit_index);
