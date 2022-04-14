// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_
#define OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_

#include <stdbool.h>
#include <stdint.h>

typedef enum {
  ibex_simple_address_translation_id_0,
  ibex_simple_address_translation_id_1,
  ibex_simple_address_translation_id_count,
} ibex_simple_address_translation_idx;

/**
 * @src_addr The source base address of the translate region
 * @size The size of the target translate block
 * @dst_addr The destination address after translation
 */
void init_translation(uint32_t src_addr, uint32_t size, uint32_t dst_addr);

/**
 * @virtual_addr The source base address of the translate region
 * @size The size of the target translate block
 * @physical_addr The destination address after translation
 */
int ibex_set_translation(ibex_simple_address_translation_idx idx,
                          uint32_t virtual_addr, uint32_t size,
                          uint32_t physical_addr);

#endif  // OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_
