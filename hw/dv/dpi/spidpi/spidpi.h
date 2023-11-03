// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_SPIDPI_SPIDPI_H_
#define OPENTITAN_HW_DV_DPI_SPIDPI_SPIDPI_H_

#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

// Bits in data to C
#define D2P_SDO 0x2
#define D2P_SDO_EN 0x1

// Bits in char from C
#define P2D_SCK 0x1
#define P2D_CSB 0x2
#define P2D_SDI 0x4

void *spidpi_create(const char *name, int mode, int loglevel);
char spidpi_tick(void *ctx_void, const svLogicVecVal *d2p_data);
void spidpi_close(void *ctx_void);

// monitor
void monitor_spi(void *mon_void, FILE *mon_file, int loglevel, int tick,
                 int p2d, int d2p);
void *monitor_spi_init(int mode);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_DV_DPI_SPIDPI_SPIDPI_H_
