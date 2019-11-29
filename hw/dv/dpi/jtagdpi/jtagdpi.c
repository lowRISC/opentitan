// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "jtagdpi.h"
#include "tcp_server.h"

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct jtagdpi_ctx {
  // Server context
  struct tcp_server_ctx *sock;
  // Signals
  uint8_t tck;
  uint8_t tms;
  uint8_t tdi;
  uint8_t tdo;
  uint8_t trst_n;
  uint8_t srst_n;
};

/**
 * Reset the JTAG signals to a "dongle unplugged" state
 */
static void reset_jtag_signals(struct jtagdpi_ctx *ctx) {
  assert(ctx);

  ctx->tck = 0;
  ctx->tms = 0;
  ctx->tdi = 0;

  // trst_n is pulled down (reset active) by default
  ctx->trst_n = 0;

  // srst_n is pulled up (reset not active) by default
  ctx->srst_n = 1;
}

/**
 * Update the JTAG signals in the context structure
 */
static void update_jtag_signals(struct jtagdpi_ctx *ctx) {
  assert(ctx);

  /*
   * Documentation pointer:
   * The remote_bitbang protocol implemented below is documented in the OpenOCD
   * source tree at doc/manual/jtag/drivers/remote_bitbang.txt, or online at
   * https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt
   */

  // read a command byte
  char cmd;
  if (!tcp_server_read(ctx->sock, &cmd)) {
    return;
  }

  bool act_send_resp = false;
  bool act_quit = false;

  // parse received command byte
  if (cmd >= '0' && cmd <= '7') {
    // JTAG write
    char cmd_bit = cmd - '0';
    ctx->tdi = (cmd_bit >> 0) & 0x1;
    ctx->tms = (cmd_bit >> 1) & 0x1;
    ctx->tck = (cmd_bit >> 2) & 0x1;
  } else if (cmd >= 'r' && cmd <= 'u') {
    // JTAG reset (active high from OpenOCD)
    char cmd_bit = cmd - 'r';
    ctx->srst_n = !((cmd_bit >> 0) & 0x1);
    ctx->trst_n = !((cmd_bit >> 1) & 0x1);
  } else if (cmd == 'R') {
    // JTAG read
    act_send_resp = true;
  } else if (cmd == 'B') {
    // printf("%s: BLINK ON!\n", ctx->display_name);
  } else if (cmd == 'b') {
    // printf("%s: BLINK OFF!\n", ctx->display_name);
  } else if (cmd == 'Q') {
    // quit (client disconnect)
    act_quit = true;
  } else {
    fprintf(stderr,
            "JTAG DPI Protocol violation detected: unsupported command %c\n",
            cmd);
    exit(1);
  }

  // send tdo as response
  if (act_send_resp) {
    char tdo_ascii = ctx->tdo + '0';
    tcp_server_write(ctx->sock, tdo_ascii);
  }

  if (act_quit) {
    printf("JTAG DPI: Remote disconnected.\n");
    tcp_server_client_close(ctx->sock);
  }
}

void *jtagdpi_create(const char *display_name, int listen_port) {
  struct jtagdpi_ctx *ctx =
      (struct jtagdpi_ctx *)calloc(1, sizeof(struct jtagdpi_ctx));
  assert(ctx);

  // Create socket
  ctx->sock = tcp_server_create(display_name, listen_port);

  reset_jtag_signals(ctx);

  printf(
      "\n"
      "JTAG: Virtual JTAG interface %s is listening on port %d. Use\n"
      "OpenOCD and the following configuration to connect:\n"
      "  interface remote_bitbang\n"
      "  remote_bitbang_host localhost\n"
      "  remote_bitbang_port %d\n",
      display_name, listen_port, listen_port);

  return (void *)ctx;
}

void jtagdpi_close(void *ctx_void) {
  struct jtagdpi_ctx *ctx = (struct jtagdpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  tcp_server_close(ctx->sock);
  free(ctx);
}

void jtagdpi_tick(void *ctx_void, svBit *tck, svBit *tms, svBit *tdi,
                  svBit *trst_n, svBit *srst_n, const svBit tdo) {
  struct jtagdpi_ctx *ctx = (struct jtagdpi_ctx *)ctx_void;

  ctx->tdo = tdo;

  // TODO: Evaluate moving this functionality into a separate thread
  if (ctx) {
    update_jtag_signals(ctx);
  }

  *tdi = ctx->tdi;
  *tms = ctx->tms;
  *tck = ctx->tck;
  *srst_n = ctx->srst_n;
  *trst_n = ctx->trst_n;
}
