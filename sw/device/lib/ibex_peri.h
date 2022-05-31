// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_
#define OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * @src_addr The source base address of the translate region
 * @size The size of the target translate block
 * @dst_addr The destination address after translation
 */
void init_translation(uint32_t src_addr, uint32_t size, uint32_t dst_addr);

/**
 * On FPGA builds, returns the value stored in the USR_ACCESS register when
 * the FPGA bitstream was built.  On non-FPGA builds, returns zero.
 */
uint32_t fpga_version(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_IBEX_PERI_H_
