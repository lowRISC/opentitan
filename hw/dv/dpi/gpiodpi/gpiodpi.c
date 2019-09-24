// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gpiodpi.h"

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

void *gpiodpi_create(const char *name, int n_bits) {
  struct gpiodpi_ctx *ctx =
      (struct gpiodpi_ctx *)calloc(1, sizeof(struct gpiodpi_ctx));
  assert(ctx);

  // n_bits > 32 requires more sophisticated handling of svBitVecVal which we
  // currently don't do.
  assert(n_bits <= 32 && "n_bits must be <= 32");

  ctx->n_bits = n_bits;

  char cwd[PATH_MAX];
  char *cwd_rv;
  cwd_rv = getcwd(cwd, sizeof(cwd));
  assert(cwd_rv != NULL);

  int rv;
  rv = snprintf(ctx->fifo_pathname, PATH_MAX, "%s/%s", cwd, name);
  assert(rv <= PATH_MAX && rv > 0);

  rv = mkfifo(ctx->fifo_pathname, 0644);  // writes are not supported currently
  if (rv != 0) {
    if (errno == EEXIST) {
      fprintf(stderr, "GPIO: Reusing existing FIFO at %s\n",
              ctx->fifo_pathname);
    } else {
      fprintf(stderr, "GPIO: Unable to create FIFO at %s: %s\n",
              ctx->fifo_pathname, strerror(errno));
      return NULL;
    }
  }

  ctx->fifo_fd = open(ctx->fifo_pathname, O_RDWR);
  if (ctx->fifo_fd < 0) {
    fprintf(stderr, "GPIO: Unable to open FIFO at %s: %s\n", ctx->fifo_pathname,
            strerror(errno));
    return NULL;
  }

  printf(
      "\n"
      "GPIO: FIFO pipe at %s for %d bit wide GPIO. Run\n"
      "$ cat %s\n"
      "to observe the output.\n",
      ctx->fifo_pathname, ctx->n_bits, ctx->fifo_pathname);

  return (void *)ctx;
}

void gpiodpi_device_to_host(void *ctx_void, svBitVecVal *gpio_data,
                            svBitVecVal *gpio_oe) {
  struct gpiodpi_ctx *ctx = (struct gpiodpi_ctx *)ctx_void;
  assert(ctx);

  // n_bits > 32 requires more sophisticated handling of svBitVecVal which we
  // currently don't do (loop through the array of 32 bit values).
  assert(ctx->n_bits <= 32 && "n_bits must be <= 32");

  char gpio_str[32 + 1];
  for (int i = 0; i < ctx->n_bits; i++) {
    gpio_str[ctx->n_bits - i - 1] = !!(gpio_data[0] & (1 << i)) + '0';
  }

  gpio_str[ctx->n_bits] = '\n';
  ssize_t written = write(ctx->fifo_fd, gpio_str, ctx->n_bits + 1);
  assert(written == ctx->n_bits + 1);
}

void gpiodpi_close(void *ctx_void) {
  struct gpiodpi_ctx *ctx = (struct gpiodpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  int rv;
  rv = close(ctx->fifo_fd);
  if (rv != 0) {
    printf("GPIO: Failed to close FIFO: %s\n", strerror(errno));
  }
  rv = unlink(ctx->fifo_pathname);
  if (rv != 0) {
    printf("GPIO: Failed to unlink FIFO file at %s: %s\n", ctx->fifo_pathname,
           strerror(errno));
  }
  free(ctx);
}
