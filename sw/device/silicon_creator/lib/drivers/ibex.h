// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Get the FPGA version value from the USR_ACCESS register.
 *
 * @return FPGA version.
 */
uint32_t ibex_fpga_version(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_IBEX_H_
