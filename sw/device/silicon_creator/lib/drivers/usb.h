// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_USB_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_USB_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/stdusb.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Flags for endpoint configuration
 */
typedef enum usb_endpoint_type {
  /** Endpoint is an IN endpoint */
  kUsbEndpointTypeIn = 1,
  /** Endpoint is a OUT endpoint */
  kUsbEndpointTypeOut = 2,
  /** Endpoint can accept SETUPDATA (e.g. a control endpoint) */
  kUsbEndpointTypeSetup = 4,
  /** Endpoint is a CONTROL endpoint */
  kUsbEndpointTypeControl = 7,
} usb_endpoint_type_t;

/**
 * Flags for managing usb transfers
 */
typedef enum usb_transfer_flags {
  /** Transfer direction is IN (device to host) */
  kUsbTransferFlagsIn = 0,
  /** Transfer direction is OUT (host to device) */
  kUsbTransferFlagsOut = 1,
  /** Transfer direction mask */
  kUsbTransferFlagsDirMask = 1,
  /** Transfer is a control transfer: requires a zero-byte packet in the
     opposite direction of the transfer to complete */
  kUsbTransferFlagsControl = 2,
  /** Transfer needs to terminate with a short or zero-byte packet. */
  kUsbTransferFlagsShortIn = 4,

  /**
   * Indicates a SETUP_DATA packet; the data argument of the callback points to
   * a usb_setup_data_t.
   */
  kUsbTransferFlagsSetupData = 0x2000,
  /**
   * Transfer is finished; the data argument of the callback points to a size_t
   * indicating the number of bytes transferred.
   */
  kUsbTransferFlagsDone = 0x4000,
  /** USB device was reset */
  kUsbTransferFlagsReset = 0x8000,
} usb_transfer_flags_t;

/**
 * Function pointer type for an endpoint handler.
 *
 * @param ctx A pointer to the context object supplied during endpoint
 *            initialization.
 * @param ep The endpoint number.
 * @param flags The usb transfer flags for this callback.
 * @param data A pointer to data relevant to this callback (see the flags).
 */
typedef void (*handler_t)(void *ctx, size_t ep, usb_transfer_flags_t flags,
                          void *data);

/**
 * An internal driver struct to manage endpoint transfers.
 */
typedef struct usb_transfer {
  /** Pointer to data to transfer. */
  char *data;
  /** Length of data remaining to transfer. */
  size_t len;
  /** Number of bytes actually transferred. */
  size_t bytes_transfered;
  /** Flags associated with this transfer. */
  usb_transfer_flags_t flags;
} usb_transfer_t;

/**
 * An internal driver struct to manage each endpoint.
 */
typedef struct usb_ep_info {
  /** The endpoint type (IN, OUT, CONTROL) */
  usb_endpoint_type_t type;
  /** The size of this endpoint. */
  uint16_t size;
  /** Any active transfer on this endpoint. */
  usb_transfer_t transfer;
  /** A handler to call for events on this endpoint. */
  handler_t handler;
  /** The user supplied context to pass to the handler. */
  void *user_ctx;
} usb_ep_info_t;

/**
 * Initialize the USB stack.
 *
 */
void usb_init(void);

/**
 * Poll the USB device, driver transfers to completion and call endpoint
 * callbacks.
 *
 */
void usb_poll(void);

/**
 * Enable USB.
 */
void usb_enable(bool en);

/**
 * Set the USB address.
 */
void usb_set_address(uint8_t device_address);

/**
 * Initialize an USB endpoint.
 *
 * @param ep The endpoint number.
 * @param type The endpoint type (IN, OUT, CONTROL).
 * @param size The endpoint size.
 * @param handler A handler to call when transactions complete on the endpoint.
 * @param user_ctx A context pointer to pass to the handler.
 */
void usb_ep_init(size_t ep, usb_endpoint_type_t type, uint16_t size,
                 handler_t handler, void *user_ctx);

/**
 * Stall or un-stall an endpoint.
 *
 * @param ep The endpoint number.
 * @param enable Whether to enable (true) or clear (false) the stall condition.
 */
void usb_ep_stall(size_t ep, bool enable);

/**
 * Return whether an endpoint is stalled.
 *
 * @param ep The endpoint number.
 * @return true if stalled.
 */
bool usb_ep_stalled(size_t ep);

/**
 * Start a transfer on an endpoint.
 *
 * @param ep The endpoint number.
 * @param data The buffer to send or receive into.
 * @param len The length of the buffer.
 * @param flags The direction or other attributes assocated with the transfer.
 */
void usb_ep_transfer(size_t ep, void *data, size_t len,
                     usb_transfer_flags_t flags);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_USB_H_
