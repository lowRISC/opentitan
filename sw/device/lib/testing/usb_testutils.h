// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "usb_testutils_diags.h"

// Result codes to rx/tx callback handlers
typedef enum {
  /**
   * Successful completion.
   */
  kUsbTestutilsXfrResultOk = 0u,
  /**
   * Failed to transfer because of internal error,
   * eg. buffer exhaustion.
   */
  kUsbTestutilsXfrResultFailed = 1u,
  /**
   * Link reset interrupted transfer.
   */
  kUsbTestutilsXfrResultLinkReset = 2u,
  /**
   * Canceled by suspend, endpoint removal or finalization.
   */
  kUsbTestutilsXfrResultCanceled = 3u,
} usb_testutils_xfr_result_t;

// Flags affecting the transfer of larger data buffers
typedef enum {
  kUsbTestutilsXfrMaxPacketMask = 0x7fu,  // Max packet size [0,0x40U]
  /**
   * Explicitly specify the maximum packet size; otherwise the device default
   * of USBDEV_MAX_PACKET_SIZE shall be assumed.
   */
  kUsbTestutilsXfrMaxPacketSupplied = 0x100u,
  /**
   * Employ double-buffering to minimize the response time to notification of
   * each packet transmission. This does require that two device packet buffers
   * be available for use, but it increases the transfer rate.
   */
  kUsbTestutilsXfrDoubleBuffered = 0x200u,
  /**
   * Emit/Expect Zero Length Packet as termination of data stage in the event
   * that the final packet of the transfer is maximum length
   */
  kUsbTestutilsXfrEmployZLP = 0x400u,
} usb_testutils_xfr_flags_t;

/* Called once send has been Acked */
typedef status_t (*usb_testutils_tx_done_handler_t)(void *,
                                                    usb_testutils_xfr_result_t);
/* Called when a packet is received*/
typedef status_t (*usb_testutils_rx_handler_t)(void *,
                                               dif_usbdev_rx_packet_info_t,
                                               dif_usbdev_buffer_t);
/* Called every 16ms based USB host timebase*/
typedef status_t (*usb_testutils_tx_flush_handler_t)(void *);
/*Called when an USB link reset is detected*/
typedef status_t (*usb_testutils_reset_handler_t)(void *);

// In-progress larger buffer transfer to/from host
typedef struct usb_testutils_transfer {
  /**
   * Start of buffer for transfer
   */
  const uint8_t *buffer;
  /**
   * Total number of bytes to be transferred to/from buffer
   */
  uint32_t length;
  /**
   * Byte offset of the _next_ packet to be transferred
   */
  uint32_t offset;
  /**
   * Flags modifying the transfer
   */
  usb_testutils_xfr_flags_t flags;
  /**
   * Indicates that the last packet of the transfer has been reached;
   * if 'next_valid' is true, then 'next_part' holds the last packet, already
   * prepared for sending; if next_valid is false, then the last packet has
   * already been supplied to usbdev and we're just awaiting the 'pkt_sent'
   * interrupt.
   */
  bool last;
  /**
   * The next part has been prepared and is ready to send to usbdev
   */
  bool next_valid;
  /**
   * When sending IN data to the host, we may employ double-buffering and keep
   * an additional buffer ready to be sent as soon as we're notified of the
   * transfer of its predecessor
   */
  dif_usbdev_buffer_t next_part;
} usb_testutils_transfer_t;

typedef struct usb_testutils_ctx usb_testutils_ctx_t;

struct usb_testutils_ctx {
  dif_usbdev_t *dev;
  dif_usbdev_buffer_pool_t *buffer_pool;
  int flushed;
  /**
   * Have we received an indication of USB activity?
   */
  bool got_frame;
  /**
   * Most recent bus frame number received from host
   */
  uint16_t frame;

  /**
   * IN endpoints
   */
  struct {
    /**
     * Opaque context handle for callback functions
     */
    void *ep_ctx;
    /**
     * Callback for transmission of IN packet
     */
    usb_testutils_tx_done_handler_t tx_done_callback;
    /**
     * Callback for periodically flushing IN data to host
     */
    usb_testutils_tx_flush_handler_t flush;
    /**
     * Callback for link reset
     */
    usb_testutils_reset_handler_t reset;
    /**
     * Current in-progress transfer, if any
     */
    usb_testutils_transfer_t transfer;
  } in[USBDEV_NUM_ENDPOINTS];

  /**
   * OUT endpoints
   */
  struct {
    /**
     * Opaque context handle for callback functions
     */
    void *ep_ctx;
    /**
     * Callback for reception of IN packet
     */
    usb_testutils_rx_handler_t rx_callback;
    /**
     * Callback for link reset
     */
    usb_testutils_reset_handler_t reset;
  } out[USBDEV_NUM_ENDPOINTS];
};

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
 * Call to set up IN endpoint.
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @param ep_ctx context pointer for callee
 * @param tx_done callback once send has been Acked
 * @param flush called every 16ms based USB host timebase
 * @param reset called when an USB link reset is detected
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_in_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep, void *ep_ctx,
    usb_testutils_tx_done_handler_t tx_done,
    usb_testutils_tx_flush_handler_t flush,
    usb_testutils_reset_handler_t reset);

/**
 * Call to set up OUT endpoint.
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @param out_mode the transfer mode for OUT transactions
 * @param ep_ctx context pointer for callee
 * @param rx called when a packet is received
 * @param reset called when an USB link reset is detected
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_out_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    usb_testutils_rx_handler_t rx, usb_testutils_reset_handler_t reset);

/**
 * Call to set up a pair of IN and OUT endpoints.
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @param out_mode the transfer mode for OUT transactions
 * @param ep_ctx context pointer for callee
 * @param tx_done callback once send has been Acked
 * @param rx called when a packet is received
 * @param flush called every 16ms based USB host timebase
 * @param reset called when an USB link reset is detected
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    usb_testutils_tx_done_handler_t tx_done, usb_testutils_rx_handler_t rx,
    usb_testutils_tx_flush_handler_t flush,
    usb_testutils_reset_handler_t reset);

/**
 * Remove an IN endpoint.
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_in_endpoint_remove(usb_testutils_ctx_t *ctx, uint8_t ep);

/**
 * Remove an OUT endpoint.
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_out_endpoint_remove(usb_testutils_ctx_t *ctx,
                                           uint8_t ep);

/**
 * Remove a pair of IN and OUT endpoints
 *
 * @param ctx usb test utils context pointer
 * @param ep endpoint number
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_endpoint_remove(usb_testutils_ctx_t *ctx, uint8_t ep);

/**
 * Initialize the usbdev interface
 *
 * Does not connect the device, since the default endpoint is not yet enabled.
 * See usb_testutils_connect().
 *
 * @param ctx uninitialized usb test utils context pointer
 * @param pinflip boolean to indicate if PHY should be configured for D+/D- flip
 * @param en_diff_rcvr boolean to indicate if PHY should enable an external
 *                     differential receiver, activating the single-ended D
 *                     input
 * @param tx_use_d_se0 boolean to indicate if PHY uses D/SE0 for TX instead of
 *                     Dp/Dn
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_init(usb_testutils_ctx_t *ctx, bool pinflip,
                            bool en_diff_rcvr, bool tx_use_d_se0);

/**
 * Send a larger data transfer from the given endpoint
 *
 * The usb_testutils layer will, if necessary, break this transfer into multiple
 * packet buffers to be transferred in turn across the USB. The caller shall be
 * notified via the tx_done_callback handler of successful completion of the
 * entire transfer, or failure, and the caller must guarantee the availability
 * of the supplied data throughout the operation.
 *
 * @param ctx        usb test utils context pointer
 * @param ep         endpoint number
 * @param data       buffer of data to be transferred
 * @param length     number of bytes to be transferred
 * @param flags      flags modifying the transfer operation
 * @return           `Ok(res)` Where `res` is true if the data has been accepted
 * for transmission.
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_transfer_send(usb_testutils_ctx_t *ctx, uint8_t ep,
                                     const uint8_t *data, uint32_t length,
                                     usb_testutils_xfr_flags_t flags);

/**
 * Call regularly to poll the usbdev interface
 *
 * @param ctx usb test utils context pointer
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_poll(usb_testutils_ctx_t *ctx);

/**
 * Finalize the usbdev interface
 *
 * Removes all endpoint handlers and disconnects the device from the USB.
 * This should be used only if the USB device is no longer required, or if it is
 * required to be restarted with, for example, a different bus configuration.
 *
 * @param ctx initialized usb test utils context pointer
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_fin(usb_testutils_ctx_t *ctx);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_H_
