// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "jtagdpi.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

struct jtag_sig_values {
  uint8_t tck;
  uint8_t tms;
  uint8_t tdi;
  uint8_t tdo;
  uint8_t trst_n;
  uint8_t srst_n;
};

struct jtagdpi_ctx {
  char *display_name;
  uint16_t listen_port;
  int sfd;  // socket fd
  int cfd;  // client fd
  struct jtag_sig_values sig;
};

/**
 * Reset the JTAG signals to a "dongle unplugged" state
 */
static void reset_jtag_signals(struct jtagdpi_ctx *ctx) {
  assert(ctx);

  ctx->sig.tck = 0;
  ctx->sig.tms = 0;
  ctx->sig.tdi = 0;

  // trst_n is pulled down (reset active) by default
  ctx->sig.trst_n = 0;

  // srst_n is pulled up (reset not active) by default
  ctx->sig.srst_n = 1;
}

/**
 * Start a TCP server
 *
 * @param ctx jtagdpi context object
 * @return 0 on success, -1 in case of an error
 */
static int tcp_server_start(struct jtagdpi_ctx *ctx) {
  int rv;

  assert(ctx->sfd == 0 && "Server already started.");

  // create socket
  int sfd = socket(AF_INET, SOCK_STREAM, 0);
  if (sfd == -1) {
    fprintf(stderr, "%s: Unable to create socket: %s (%d)\n", ctx->display_name,
            strerror(errno), errno);
    return -1;
  }

  rv = fcntl(sfd, F_SETFL, O_NONBLOCK);
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to make socket non-blocking: %s (%d)\n",
            ctx->display_name, strerror(errno), errno);
    return -1;
  }

  // reuse existing socket (if existing)
  int reuse_socket = 1;
  rv = setsockopt(sfd, SOL_SOCKET, SO_REUSEADDR, &reuse_socket, sizeof(int));
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to set socket options: %s (%d)\n",
            ctx->display_name, strerror(errno), errno);
    return -1;
  }

  // bind server
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_ANY);
  addr.sin_port = htons(ctx->listen_port);

  rv = bind(sfd, (struct sockaddr *)&addr, sizeof(addr));
  if (rv != 0) {
    fprintf(stderr, "%s: Failed to bind socket: %s (%d)\n", ctx->display_name,
            strerror(errno), errno);
    return -1;
  }

  // listen for incoming connections
  rv = listen(sfd, 1);
  if (rv != 0) {
    fprintf(stderr, "%s: Failed to listen on socket: %s (%d)\n",
            ctx->display_name, strerror(errno), errno);
    return -1;
  }

  ctx->sfd = sfd;
  assert(ctx->sfd > 0);

  return 0;
}

/**
 * Accept an incoming connection from a client (nonblocking)
 *
 * The resulting client fd is made non-blocking.
 *
 * @param ctx jtagdpi context object
 * @return 0 on success, any other value indicates an error
 */
static int tcp_server_client_tryaccept(struct jtagdpi_ctx *ctx) {
  int rv;

  assert(ctx->sfd > 0);
  assert(ctx->cfd == 0);

  int cfd = accept(ctx->sfd, NULL, NULL);

  if (cfd == -1 && errno == EAGAIN) {
    return -EAGAIN;
  }

  if (cfd == -1) {
    fprintf(stderr, "%s: Unable to accept incoming connection: %s (%d)\n",
            ctx->display_name, strerror(errno), errno);
    return -1;
  }

  rv = fcntl(cfd, F_SETFL, O_NONBLOCK);
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to make client socket non-blocking: %s (%d)\n",
            ctx->display_name, strerror(errno), errno);
    return -1;
  }

  ctx->cfd = cfd;
  assert(ctx->cfd > 0);

  printf("%s: Accepted client connection\n", ctx->display_name);

  return 0;
}

static void tcp_server_client_close(struct jtagdpi_ctx *ctx) {
  assert(ctx);

  reset_jtag_signals(ctx);

  if (!ctx->cfd) {
    return;
  }

  close(ctx->cfd);
  ctx->cfd = 0;
}

static void tcp_server_stop(struct jtagdpi_ctx *ctx) {
  assert(ctx);
  if (ctx->sfd) {
    return;
  }
  close(ctx->sfd);
  ctx->sfd = 0;
}

/**
 * Update the JTAG signals in the context structure
 */
static void update_jtag_signals(struct jtagdpi_ctx *ctx) {
  assert(ctx);

  ssize_t num_read;
  bool act_send_resp = false;
  bool act_quit = false;

  if (ctx->sfd == 0) {
    // Not connected yet
    return;
  }

  // accept (possibly) incoming connection
  if (ctx->cfd == 0) {
    int rv = tcp_server_client_tryaccept(ctx);
    if (rv != 0) {
      // Unable to accept incoming connection (not necessarily an error).
      // Try again in the next cycle.
      return;
    }
  }
  assert(ctx->cfd > 0);

  /*
   * Documentation pointer:
   * The remote_bitbang protocol implemented below is documented in the OpenOCD
   * source tree at doc/manual/jtag/drivers/remote_bitbang.txt, or online at
   * https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt
   */

  // read a command byte
  char cmd;
  num_read = read(ctx->cfd, &cmd, sizeof(cmd));
  if (num_read == 0) {
    return;
  }
  if (num_read == -1) {
    if (errno == EAGAIN || errno == EWOULDBLOCK) {
      return;
    } else if (errno == EBADF) {
      // Possibly client went away? Accept a new connection.
      fprintf(stderr, "%s: Client disappeared.\n", ctx->display_name);
      tcp_server_client_close(ctx);
      return;
    } else {
      fprintf(stderr, "%s: Error while reading from client: %s (%d)\n",
              ctx->display_name, strerror(errno), errno);
      assert(0 && "Error reading from client");
    }
  }
  assert(num_read == 1);

  // parse received command byte
  if (cmd >= '0' && cmd <= '7') {
    // JTAG write
    char cmd_bit = cmd - '0';
    ctx->sig.tdi = (cmd_bit >> 0) & 0x1;
    ctx->sig.tms = (cmd_bit >> 1) & 0x1;
    ctx->sig.tck = (cmd_bit >> 2) & 0x1;
  } else if (cmd >= 'r' && cmd <= 'u') {
    // JTAG reset (active high from OpenOCD)
    char cmd_bit = cmd - 'r';
    ctx->sig.srst_n = !((cmd_bit >> 0) & 0x1);
    ctx->sig.trst_n = !((cmd_bit >> 1) & 0x1);
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
    fprintf(stderr, "%s: Protocol violation detected: unsupported command %c\n",
            ctx->display_name, cmd);
    exit(1);
  }

  // send tdo as response
  if (act_send_resp) {
    char tdo_ascii = ctx->sig.tdo + '0';
    while (1) {
      ssize_t num_written =
          send(ctx->cfd, &tdo_ascii, sizeof(tdo_ascii), MSG_NOSIGNAL);
      if (num_written == -1) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
          continue;
        } else if (errno == EPIPE) {
          act_quit = true;
          break;
        } else {
          fprintf(stderr, "%s: Error while writing to client: %s (%d)\n",
                  ctx->display_name, strerror(errno), errno);
          assert(0 && "Error writing to client.");
        }
      }
      if (num_written >= 1) {
        break;
      }
    }
  }

  if (act_quit) {
    printf("%s: Remote disconnected.\n", ctx->display_name);
    tcp_server_client_close(ctx);
  }
}

void *jtagdpi_create(const char *display_name, int listen_port) {
  struct jtagdpi_ctx *ctx =
      (struct jtagdpi_ctx *)calloc(1, sizeof(struct jtagdpi_ctx));
  assert(ctx);

  ctx->listen_port = listen_port;
  ctx->display_name = strdup(display_name);
  assert(ctx->display_name);

  reset_jtag_signals(ctx);

  int rv = tcp_server_start(ctx);
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to create TCP server on port %d\n",
            ctx->display_name, ctx->listen_port);
    goto err_cleanup_return;
  }

  printf(
      "\n"
      "JTAG: Virtual JTAG interface %s is listening on port %d. Use\n"
      "OpenOCD and the following configuration to connect:\n"
      "  interface remote_bitbang\n"
      "  remote_bitbang_host localhost\n"
      "  remote_bitbang_port %d\n",
      ctx->display_name, ctx->listen_port, ctx->listen_port);

  return (void *)ctx;

err_cleanup_return:
  free(ctx->display_name);
  free(ctx);
  return NULL;
}

void jtagdpi_close(void *ctx_void) {
  struct jtagdpi_ctx *ctx = (struct jtagdpi_ctx *)ctx_void;
  if (!ctx) {
    return;
  }
  tcp_server_client_close(ctx);
  tcp_server_stop(ctx);

  free(ctx->display_name);
  free(ctx);
}

void jtagdpi_tick(void *ctx_void, svBit *tck, svBit *tms, svBit *tdi,
                  svBit *trst_n, svBit *srst_n, const svBit tdo) {
  struct jtagdpi_ctx *ctx = (struct jtagdpi_ctx *)ctx_void;

  ctx->sig.tdo = tdo;

  // TODO: Evaluate moving this functionality into a separate thread
  if (ctx) {
    update_jtag_signals(ctx);
  }

  *tdi = ctx->sig.tdi;
  *tms = ctx->sig.tms;
  *tck = ctx->sig.tck;
  *srst_n = ctx->sig.srst_n;
  *trst_n = ctx->sig.trst_n;
}
