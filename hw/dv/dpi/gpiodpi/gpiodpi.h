// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef GPIODPI_H_
#define GPIODPI_H_

#include <limits.h>
#include <svdpi.h>

extern "C" {

struct gpiodpi_ctx {
  int n_bits;
  int fifo_fd;
  char fifo_pathname[PATH_MAX];
};

void *gpiodpi_create(const char *name, int n_bits);
void gpiodpi_device_to_host(void *ctx_void, svBitVecVal *gpio_data,
                            svBitVecVal *gpio_oe);
void gpiodpi_close(void *ctx_void);
}
#endif  // GPIODPI_H_
