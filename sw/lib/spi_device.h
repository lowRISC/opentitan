// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _SPI_DEVICE_H_
#define _SPI_DEVICE_H_

#include <stddef.h>

#include "common.h"

#define SPI_DEVICE0_BASE_ADDR 0x40020000

#include "spi_device_regs.h"

#define SPID_SRAM_ADDR SPI_DEVICE_BUFFER(SPI_DEVICE0_BASE_ADDR)
#define SPID_RXF_BASE 0x000
#define SPID_RXF_SIZE 0x400
#define SPID_TXF_BASE 0x600
#define SPID_TXF_SIZE 0x200

#define SPID_SRAM_SIZE (0x800)

/* Note: these will correctly remove the phase bit */
#define READ32_RXFPTR(P) \
  REG32(SPID_SRAM_ADDR + SPID_RXF_BASE + ((P) & (SPID_RXF_SIZE - 1)))

#define ACCESS32_TXFPTR(P) \
  REG32(SPID_SRAM_ADDR + SPID_TXF_BASE + ((P) & ((SPID_TXF_SIZE - 1) & ~0x3)))

void spid_init(void);
size_t spid_send(void *data, size_t len_bytes);
size_t spid_read_nb(void *data, size_t len);

#endif /* _SPI_DEVICE_H_ */
