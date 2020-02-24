// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "tcp_server.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

/**
 * Simple buffer for passing data between TCP sockets and DPI modules
 */
const int BUFSIZE_BYTE = 256;

struct tcp_buf {
  unsigned int rptr;
  unsigned int wptr;
  char buf[BUFSIZE_BYTE];
};

/**
 * TCP Server thread context structure
 */
struct tcp_server_ctx {
  // Writeable by the host thread
  char *display_name;
  uint16_t listen_port;
  volatile bool socket_run;
  // Writeable by the server thread
  tcp_buf *buf_in;
  tcp_buf *buf_out;
  int sfd;  // socket fd
  int cfd;  // client fd
  pthread_t sock_thread;
};

static bool tcp_buffer_is_full(struct tcp_buf *buf) {
  if (buf->wptr >= buf->rptr) {
    return (buf->wptr - buf->rptr) == (BUFSIZE_BYTE - 1);
  } else {
    return (buf->rptr - buf->wptr) == 1;
  }
}

static bool tcp_buffer_is_empty(struct tcp_buf *buf) {
  return (buf->wptr == buf->rptr);
}

static void tcp_buffer_put_byte(struct tcp_buf *buf, char dat) {
  bool done = false;
  while (!done) {
    if (!tcp_buffer_is_full(buf)) {
      buf->buf[buf->wptr++] = dat;
      buf->wptr %= BUFSIZE_BYTE;
      done = true;
    }
  }
}

static bool tcp_buffer_get_byte(struct tcp_buf *buf, char *dat) {
  if (tcp_buffer_is_empty(buf)) {
    return false;
  }
  *dat = buf->buf[buf->rptr++];
  buf->rptr %= BUFSIZE_BYTE;
  return true;
}

static struct tcp_buf *tcp_buffer_new(void) {
  struct tcp_buf *buf_new;
  buf_new = (struct tcp_buf *)malloc(sizeof(struct tcp_buf));
  buf_new->rptr = 0;
  buf_new->wptr = 0;
  return buf_new;
}

static void tcp_buffer_free(struct tcp_buf **buf) {
  free(*buf);
  *buf = NULL;
}

/**
 * Start a TCP server
 *
 * This function creates attempts to create a new TCP socket instance. The
 * socket is a non-blocking stream socket, with buffering disabled.
 *
 * @param ctx context object
 * @return 0 on success, -1 in case of an error
 */
static int start(struct tcp_server_ctx *ctx) {
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

  // stop tcp socket from buffering (buffering prevents timely responses to
  // OpenOCD which severly limits debugging performance)
  int tcp_nodelay = 1;
  rv = setsockopt(sfd, IPPROTO_TCP, TCP_NODELAY, &tcp_nodelay, sizeof(int));
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to set socket nodelay: %s (%d)\n",
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
 * @param ctx context object
 * @return 0 on success, any other value indicates an error
 */
static int client_tryaccept(struct tcp_server_ctx *ctx) {
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

/**
 * Stop the TCP server
 *
 * @param ctx context object
 */
static void stop(struct tcp_server_ctx *ctx) {
  assert(ctx);
  if (!ctx->sfd) {
    return;
  }
  close(ctx->sfd);
  ctx->sfd = 0;
}

/**
 * Receive a byte from a connected client
 *
 * @param ctx context object
 * @param cmd byte received
 * @return true if a byte was read
 */
static bool get_byte(struct tcp_server_ctx *ctx, char *cmd) {
  assert(ctx);

  ssize_t num_read = read(ctx->cfd, cmd, 1);

  if (num_read == 0) {
    return false;
  }
  if (num_read == -1) {
    if (errno == EAGAIN || errno == EWOULDBLOCK) {
      return false;
    } else if (errno == EBADF) {
      // Possibly client went away? Accept a new connection.
      fprintf(stderr, "%s: Client disappeared.\n", ctx->display_name);
      tcp_server_client_close(ctx);
      return false;
    } else {
      fprintf(stderr, "%s: Error while reading from client: %s (%d)\n",
              ctx->display_name, strerror(errno), errno);
      assert(0 && "Error reading from client");
    }
  }
  assert(num_read == 1);
  return true;
}

/**
 * Send a byte to a connected client
 *
 * @param ctx context object
 * @param cmd byte to send
 */
static void put_byte(struct tcp_server_ctx *ctx, char cmd) {
  while (1) {
    ssize_t num_written = send(ctx->cfd, &cmd, sizeof(cmd), MSG_NOSIGNAL);
    if (num_written == -1) {
      if (errno == EAGAIN || errno == EWOULDBLOCK) {
        continue;
      } else if (errno == EPIPE) {
        printf("%s: Remote disconnected.\n", ctx->display_name);
        tcp_server_client_close(ctx);
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

/**
 * Cleanup server context
 *
 * @param ctx context object
 */
static void ctx_free(struct tcp_server_ctx *ctx) {
  // Free the buffers
  tcp_buffer_free(&ctx->buf_in);
  tcp_buffer_free(&ctx->buf_out);
  // Free the display name
  free(ctx->display_name);
  // Free the ctx
  free(ctx);
  ctx = NULL;
}

/**
 * Thread function to create a new server instance
 *
 * @param ctx_void context object
 * @return Always returns NULL
 */
static void *server_create(void *ctx_void) {
  // Cast to a server struct
  struct tcp_server_ctx *ctx = (struct tcp_server_ctx *)ctx_void;
  struct timeval timeout;

  // Start the server
  int rv = start(ctx);
  if (rv != 0) {
    fprintf(stderr, "%s: Unable to create TCP server on port %d\n",
            ctx->display_name, ctx->listen_port);
    goto err_cleanup_return;
  }

  // Initialise timeout
  timeout.tv_sec = 0;

  // Initialise fd_set

  // Start waiting for connection / data
  char xfer_data;
  while (ctx->socket_run) {
    // Initialise structure of fds
    fd_set read_fds;
    FD_ZERO(&read_fds);
    if (ctx->sfd) {
      FD_SET(ctx->sfd, &read_fds);
    }
    if (ctx->cfd) {
      FD_SET(ctx->cfd, &read_fds);
    }
    // max fd num
    int mfd = (ctx->cfd > ctx->sfd) ? ctx->cfd : ctx->sfd;

    // Set timeout - 50us gives good performance
    timeout.tv_usec = 50;

    // Wait for socket activity or timeout
    rv = select(mfd + 1, &read_fds, NULL, NULL, &timeout);

    if (rv < 0) {
      printf("%s: Socket read failed, port: %d\n", ctx->display_name,
             ctx->listen_port);
      tcp_server_client_close(ctx);
    }

    // New connection
    if (FD_ISSET(ctx->sfd, &read_fds)) {
      client_tryaccept(ctx);
    }

    // New client data
    if (FD_ISSET(ctx->cfd, &read_fds)) {
      while (get_byte(ctx, &xfer_data)) {
        tcp_buffer_put_byte(ctx->buf_in, xfer_data);
      }
    }

    if (ctx->cfd != 0) {
      while (tcp_buffer_get_byte(ctx->buf_out, &xfer_data)) {
        put_byte(ctx, xfer_data);
      }
    }
  }

err_cleanup_return:

  // Simulation done - clean up
  tcp_server_client_close(ctx);
  stop(ctx);

  return NULL;
}

// Abstract interface functions
tcp_server_ctx *tcp_server_create(const char *display_name, int listen_port) {
  struct tcp_server_ctx *ctx =
      (struct tcp_server_ctx *)calloc(1, sizeof(struct tcp_server_ctx));
  assert(ctx);

  // Create the buffers
  struct tcp_buf *buf_in = tcp_buffer_new();
  struct tcp_buf *buf_out = tcp_buffer_new();
  assert(buf_in);
  assert(buf_out);

  // Populate the struct with buffer pointers
  ctx->buf_in = buf_in;
  ctx->buf_out = buf_out;

  // Set up socket details
  ctx->socket_run = true;
  ctx->listen_port = listen_port;
  ctx->display_name = strdup(display_name);
  assert(ctx->display_name);

  if (pthread_create(&ctx->sock_thread, NULL, server_create, (void *)ctx) !=
      0) {
    fprintf(stderr, "%s: Unable to create TCP socket thread\n",
            ctx->display_name);
    ctx_free(ctx);
    free(ctx);
    return NULL;
  }
  return ctx;
}

bool tcp_server_read(struct tcp_server_ctx *ctx, char *dat) {
  return tcp_buffer_get_byte(ctx->buf_in, dat);
}

void tcp_server_write(struct tcp_server_ctx *ctx, char dat) {
  tcp_buffer_put_byte(ctx->buf_out, dat);
}

void tcp_server_close(struct tcp_server_ctx *ctx) {
  // Shut down the socket thread
  ctx->socket_run = false;
  pthread_join(ctx->sock_thread, NULL);
  ctx_free(ctx);
}

void tcp_server_client_close(struct tcp_server_ctx *ctx) {
  assert(ctx);

  if (!ctx->cfd) {
    return;
  }

  close(ctx->cfd);
  ctx->cfd = 0;
}
