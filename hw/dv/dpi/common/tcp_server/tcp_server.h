// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Functions to create and interact with a threaded TCP server
 *
 * This is intended to be used by simulation add-on DPI modules to provide
 * basic TCP socket communication between a host and simulated peripherals.
 */

#ifndef TCP_SERVER_H_
#define TCP_SERVER_H_

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

struct tcp_server_ctx;

/**
 * Non-blocking read of a byte from a connected client
 *
 * @param ctx tcp server context object
 * @param dat byte received
 * @return true if a byte was read
 */
bool tcp_server_read(struct tcp_server_ctx *ctx, char *dat);

/**
 * Write a byte to a connected client
 *
 * The write is internally buffered and so does not block if the client is not
 * ready to accept data, but does block if the buffer is full.
 *
 * @param ctx tcp server context object
 * @param dat byte to send
 */
void tcp_server_write(struct tcp_server_ctx *ctx, char dat);

/**
 * Create a new TCP server instance
 *
 * @param display_name C string description of server
 * @param listen_port On which port the server should listen
 * @return A pointer to the created context struct
 */
tcp_server_ctx *tcp_server_create(const char *display_name, int listen_port);

/**
 * Shut down the server and free all reserved memory
 *
 * @param ctx tcp server context object
 */
void tcp_server_close(struct tcp_server_ctx *ctx);

/**
 * Instruct the server to disconnect a client
 *
 * @param ctx tcp server context object
 */
void tcp_server_client_close(struct tcp_server_ctx *ctx);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // TCP_SERVER_H_
