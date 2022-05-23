// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_USBDEV_H_
#define OPENTITAN_SW_DEVICE_LIB_USBDEV_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

// Hardware parameters
#define NUM_BUFS 32
#define BUF_LENGTH 64
#define NUM_ENDPOINTS 12

// USB buffers are held in the SRAM in the interface, referenced by ID
// Buffer IDs are 0 to NUM_BUFS
// Use negative buffer ID for error
typedef int usbbufid_t;
typedef struct usbdev_ctx usbdev_ctx_t;

// Note: this is only needed here because the caller of init needs it
struct usbdev_ctx {
  // TODO: base_addr goes here once header files support using it
  int can_wake;
  uint8_t freebuf[NUM_BUFS];
  uint32_t halted;  // bit vector per endpoint
  int nfree;
  int flushed;
  usbdev_ctx_t *ep_ctx[NUM_ENDPOINTS];
  void (*tx_done_callback[NUM_ENDPOINTS])(void *);
  void (*rx_callback[NUM_ENDPOINTS])(void *, usbbufid_t, int, int);
  void (*flush[NUM_ENDPOINTS])(void *);
  void (*reset[NUM_ENDPOINTS])(void *);
};

/**
 * Select USB lines P or N
 */
typedef enum line_sel { kDpSel = 0, kDnSel = 1 } line_sel_t;

/**
 * Allocate a buffer for the caller to use
 *
 * @param ctx usbdev context pointer
 * @return buffer ID or negative for out of buffer error
 */
usbbufid_t usbdev_buf_allocate_byid(usbdev_ctx_t *ctx);

/**
 * Free a buffer when caller no longer needs it
 *
 * @param ctx usbdev context pointer
 * @param buf buffer ID being returned to free pool
 * @return 0 or -1 if the free pool is full (shouldn't happen)
 */
int usbdev_buf_free_byid(usbdev_ctx_t *ctx, usbbufid_t buf);

/**
 * Get memory address for accessing data in a buffer
 *
 * Hardware restriction: buffer can only be written with 32-bit words
 * Ok to cast the return value to int8_t * for reading
 *
 * @param ctx usbdev context pointer
 * @param buf buffer ID to access
 * @return pointer to access the data of @p buf
 */
uint32_t *usbdev_buf_idtoaddr(usbdev_ctx_t *ctx, usbbufid_t buf);

/**
 * Copy from memory into a buffer, referencing by buffer ID
 *
 * Implementation restriction: from must be 4-byte aligned
 * TODO remove restriction
 *
 * @param ctx usbdev context pointer
 * @param buf buffer ID to copy to
 * @param from source address for data
 * @param len_bytes length in bytes of data to copy
 */
void usbdev_buf_copyto_byid(usbdev_ctx_t *ctx, usbbufid_t buf, const void *from,
                            size_t len_bytes);

/**
 * Schedule a buffer for transmission on an endpoint
 *
 * Send happens on next IN request for that endpoint from the host.
 * Once this call is made the buffer is owned by the hardware
 *
 * @param ctx usbdev context pointer
 * @param buf buffer ID to send
 * @param size length in bytes of data to send, zero is valid (used as ack)
 * @param endpoint endpoint to send from
 */
void usbdev_sendbuf_byid(usbdev_ctx_t *ctx, usbbufid_t buf, size_t size,
                         int endpoint);

/**
 * Call regularly to poll the usbdev interface
 *
 * @param ctx usbdev context pointer
 */
void usbdev_poll(usbdev_ctx_t *ctx);

/**
 * Get the content of the USB status register
 * @param ctx usbdev context pointer
 * @return USB status register
 */
unsigned int usbdev_get_status(usbdev_ctx_t *ctx);

/**
 * Get the current USB link state
 * @param ctx usbdev context pointer
 * @return USB link state
 */
unsigned int usbdev_get_link_state(usbdev_ctx_t *ctx);

/**
 * Get the current USB address
 * @param ctx usbdev context pointer
 * @return USB address
 */
unsigned int usbdev_get_address(usbdev_ctx_t *ctx);

/**
 * Set the USB device ID
 *
 * Device ID must be zero at init. When the host assigns an ID
 * with a SET_ADDRESS packet and the complete SETUP transaction is
 * complete, this function should be called to set the new ID. Note
 * on a reset the hardware will clear the device ID back to 0.
 *
 * @param ctx usbdev context pointer
 * @param deviceid new deviceid
 */
void usbdev_set_deviceid(usbdev_ctx_t *ctx, int deviceid);

/**
 * Halt or release an endpoint
 *
 * By default endpoints are enabled, but they can be halted but the host
 *
 * @param ctx usbdev context pointer
 * @param endpoint number
 * @param enable set/clear
 */
void usbdev_halt(usbdev_ctx_t *ctx, int endpoint, int enable);

/**
 * Get halted status for an endpoint
 *
 * @param ctx usbdev context pointer
 * @param endpoint number
 * @return 1 if endpoint is halted else 0
 */
inline int usbdev_halted(usbdev_ctx_t *ctx, int endpoint) {
  return (ctx->halted >> endpoint) & 0x1;
}

/**
 * Configure an endpoint as ISO / non-ISO
 *
 * By default endpoints are non-ISO, but they can be set to ISO
 *
 * @param ctx usbdev context pointer
 * @param endpoint number
 * @param enable 0: non-ISO, 1: ISO
 */
void usbdev_set_iso(usbdev_ctx_t *ctx, int endpoint, int enable);

/**
 * Clear the data toggle bit for an endpoint
 * @param ctx usbdev context pointer
 * @param endpoint Endpoint number
 */
void usbdev_clear_data_toggle(usbdev_ctx_t *ctx, int endpoint);

/**
 * Updates the stall setting for EP0. If stall is set then an IN, or
 * OUT transaction to EP0 will be responded to with a STALL return. This
 * flag is cleared on a a SETUP transaction
 * @param ctx usbdev context pointer
 * @param stall
 */
void usbdev_set_ep0_stall(usbdev_ctx_t *ctx, int stall);

/**
 * Enable or disable remote wake
 *
 * @param ctx usbdev context pointer
 * @param enable set/clear
 */
inline void usbdev_rem_wake_en(usbdev_ctx_t *ctx, int enable) {
  ctx->can_wake = (enable) ? 1 : 0;
}

/**
 * Get ability to wake the host
 *
 * @param ctx usbdev context pointer
 * @return 1 if remote wake is permitted else 0
 */
int usbdev_can_rem_wake(usbdev_ctx_t *ctx);

/**
 * Re-enable OUT transactions for a given endpoint.
 *
 * This function must be called after reception of a packet for a given
 * endpoint, else the endpoint will NAK the next packet.
 *
 * @param ctx usbdev context pointer
 * @param endpoint endpoint number
 */
void usbdev_clear_out_nak(usbdev_ctx_t *ctx, int ep);

typedef enum usbdev_out_transfer_mode {
  /**
   * The endpoint does not support OUT transactions.
   */
  kUsbdevOutDisabled = 0,
  /**
   * Software does NOT need to call usbdev_clear_out_nak() after every received
   * transaction. If software takes no action, usbdev will allow an endpoint's
   * transactions to proceed as long as a buffer is available.
   */
  kUsbdevOutStream = 1,
  /**
   * Software must call usbdev_clear_out_nak() after every received transaction
   * to re-enable packet reception. This gives software time to respond with the
   * appropriate handshake when it's ready.
   */
  kUsbdevOutMessage = 2,
} usbdev_out_transfer_mode_t;

/**
 * Call to setup an endpoint
 *
 * @param ctx usbdev context pointer
 * @param ep endpoint number
 * @param out_mode the transfer mode for OUT transactions
 * @param ep_ctx context pointer for callee
 * @param tx_done(void *ep_ctx) callback once send has been Acked
 * @param rx(void *ep_ctx, usbbufid_t buf, int size, int setup)
          called when a packet is received
 * @param flush(void *ep_ctx) called every 16ms based USB host timebase
 * @param reset(void *ep_ctx) called when an USB link reset is detected
 */
void usbdev_endpoint_setup(usbdev_ctx_t *ctx, int ep,
                           usbdev_out_transfer_mode_t out_mode, void *ep_ctx,
                           void (*tx_done)(void *),
                           void (*rx)(void *, usbbufid_t, int, int),
                           void (*flush)(void *), void (*reset)(void *));

/**
 * Connect the device to the bus.
 *
 * @param ctx the usbdev context.
 */
void usbdev_connect(usbdev_ctx_t *ctx);

/**
 * Initialize the usbdev interface
 *
 * Does not connect the device, since the default endpoint is not yet enabled.
 * See usbdev_connect().
 *
 * @param ctx uninitialized usbdev context pointer
 * @param pinflip boolean to indicate if PHY should be configured for D+/D- flip
 * @param en_diff_rcvr boolean to indicate if PHY should enable an external
 *                     differential receiver, activating the single-ended D
 *                     input
 * @param tx_use_d_se0 boolean to indicate if PHY uses D/SE0 for TX instead of
 *                     Dp/Dn
 */
void usbdev_init(usbdev_ctx_t *ctx, bool pinflip, bool en_diff_rcvr,
                 bool tx_use_d_se0);

/**
 * Force usbdev to output suspend state for testing purposes
 */
void usbdev_force_suspend(void);

/**
 * Force usbdev pull-up to specific value
 */
void usbdev_force_dx_pullup(line_sel_t line, bool set);

/**
 * Enable usb wake module to go active / inactive.
 */
void usbdev_set_wake_module_active(bool set);

// Used for tracing what is going on. This may impact timing which is critical
// when simulating with the USB DPI module.
//#define ENABLE_TRC
#ifdef ENABLE_TRC
#include "sw/device/lib/runtime/log.h"
#define TRC_S(s) LOG_INFO("%s", s)
#define TRC_I(i, b) LOG_INFO("0x%x", i)
#define TRC_C(c) LOG_INFO("%c", c)
#else
#define TRC_S(s)
#define TRC_I(i, b)
#define TRC_C(c)
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_USBDEV_H_
