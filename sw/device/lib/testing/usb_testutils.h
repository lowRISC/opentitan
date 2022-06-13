// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_usbdev.h"

typedef struct usb_testutils_ctx usb_testutils_ctx_t;

struct usb_testutils_ctx {
  dif_usbdev_t *dev;
  dif_usbdev_buffer_pool_t *buffer_pool;
  int flushed;
  void *ep_ctx[USBDEV_NUM_ENDPOINTS];
  void (*tx_done_callback[USBDEV_NUM_ENDPOINTS])(void *);
  void (*rx_callback[USBDEV_NUM_ENDPOINTS])(void *, dif_usbdev_rx_packet_info_t,
                                            dif_usbdev_buffer_t);
  void (*flush[USBDEV_NUM_ENDPOINTS])(void *);
  void (*reset[USBDEV_NUM_ENDPOINTS])(void *);
};

/**
 * Call regularly to poll the usbdev interface
 *
 * @param ctx usbdev context pointer
 */
void usb_testutils_poll(usb_testutils_ctx_t *ctx);

typedef enum usb_testutils_out_transfer_mode {
  /**
   * The endpoint does not support OUT transactions.
   */
  kUsbdevOutDisabled = 0,
  /**
   * Software does NOT need to call usb_testutils_clear_out_nak() after every
   * received transaction. If software takes no action, usbdev will allow an
   * endpoint's transactions to proceed as long as a buffer is available.
   */
  kUsbdevOutStream = 1,
  /**
   * Software must call usb_testutils_clear_out_nak() after every received
   * transaction to re-enable packet reception. This gives software time to
   * respond with the appropriate handshake when it's ready.
   */
  kUsbdevOutMessage = 2,
} usb_testutils_out_transfer_mode_t;

/**
 * Call to set up endpoints.
 *
 * Note that this library currently only supports setting up both the IN and OUT
 * endpoints in the same call, using the same `ep_ctx` for their callbacks.
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
void usb_testutils_endpoint_setup(usb_testutils_ctx_t *ctx, int ep,
                                  usb_testutils_out_transfer_mode_t out_mode,
                                  void *ep_ctx, void (*tx_done)(void *),
                                  void (*rx)(void *,
                                             dif_usbdev_rx_packet_info_t,
                                             dif_usbdev_buffer_t),
                                  void (*flush)(void *), void (*reset)(void *));

/**
 * Initialize the usbdev interface
 *
 * Does not connect the device, since the default endpoint is not yet enabled.
 * See usb_testutils_connect().
 *
 * @param ctx uninitialized usbdev context pointer
 * @param pinflip boolean to indicate if PHY should be configured for D+/D- flip
 * @param en_diff_rcvr boolean to indicate if PHY should enable an external
 *                     differential receiver, activating the single-ended D
 *                     input
 * @param tx_use_d_se0 boolean to indicate if PHY uses D/SE0 for TX instead of
 *                     Dp/Dn
 */
void usb_testutils_init(usb_testutils_ctx_t *ctx, bool pinflip,
                        bool en_diff_rcvr, bool tx_use_d_se0);

// Used for tracing what is going on. This may impact timing which is critical
// when simulating with the USB DPI module.
// #define ENABLE_TRC
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

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_
