// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "uartdpi.h"

#ifdef __linux__
#include <pty.h>
#elif __APPLE__
#include <util.h>
#endif

#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void *uartdpi_create(const char *name) {
  struct uartdpi_ctx *ctx =
      (struct uartdpi_ctx *)malloc(sizeof(struct uartdpi_ctx));
  assert(ctx);

  int rv;

  struct termios tty;
  cfmakeraw(&tty);

  rv = openpty(&ctx->master, &ctx->slave, 0, &tty, 0);
  assert(rv != -1);

  rv = ttyname_r(ctx->slave, ctx->ptyname, 64);
  assert(rv == 0 && "ttyname_r failed");

  int cur_flags = fcntl(ctx->master, F_GETFL, 0);
  assert(cur_flags != -1 && "Unable to read current flags.");
  int new_flags = fcntl(ctx->master, F_SETFL, cur_flags | O_NONBLOCK);
  assert(new_flags != -1 && "Unable to set FD flags");

  printf(
      "\n"
      "UART: Created %s for %s. Connect to it with any terminal program, e.g.\n"
      "$ screen %s\n",
      ctx->ptyname, name, ctx->ptyname);

  return (void *)ctx;
}

int uartdpi_can_read(void *ctx_void) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;

  int rv = read(ctx->master, &ctx->tmp_read, 1);
  return (rv == 1);
}

char uartdpi_read(void *ctx_void) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;

  return ctx->tmp_read;
}

void uartdpi_write(void *ctx_void, char c) {
  struct uartdpi_ctx *ctx = (struct uartdpi_ctx *)ctx_void;

  int rv = write(ctx->master, &c, 1);
  assert(rv == 1 && "write() failed.");
}
