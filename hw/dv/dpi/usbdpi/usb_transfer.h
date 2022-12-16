// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
#include <stdint.h>

// USBDEV IP block supports up to 64-bytes/packet
#ifndef USBDEV_MAX_PACKET_SIZE
#define USBDEV_MAX_PACKET_SIZE 64U
#endif

// Maximal length of a byte sequence to be transmitted/receive without
// interruption or pause (Start Of Frame, Setup packet, OUT Data packet
// and End Of Frame all back-to-back?)
#define USBDPI_MAX_DATA (3U + 3U + 1U + USBDEV_MAX_PACKET_SIZE + 2U + 1U)

/**
 * Forwards reference to usbpdi state context
 */
typedef struct usbdpi_ctx usbdpi_ctx_t;

/**
 * Description of data transferred over the USB by the DPI model;
 *
 * NOte: this is not to be confused with a Transfer in the terminology of the
 * USB. With the current fixed behavior of the DPI model, 'usbdpi_transfer'
 * holds a single contiguous sequence of bytes to be transferred in one
 * direction without any response.
 *
 * TODO - As the functionality of the DPI model is extended, it is anticipated
 * that this container may be extended to hold multiple Stages, forming multiple
 * Transactions and perhaps ultimately an entire Transfer. It would then contain
 * also the state information recording progress through the Transfer, allowing
 * the DPI model to switch among multiple 'in progress' transfers as required.
 */
typedef struct usbdpi_transfer usbdpi_transfer_t;

struct usbdpi_transfer {
  /**
   * Received transfers are linked together in the order of receipt
   */
  usbdpi_transfer_t *next;
  /**
   * Number of bytes to be transmitted/received
   */
  uint8_t num_bytes;
  /**
   * Offset of the PID of the data stage (or USBDPI_NO_DATA_STAGE if none)
   */
  uint8_t data_start;
  /**
   * Bytes being transferred (Note: this includes PID and CRCs; it is _not_ just
   * the data field)
   */
  uint8_t data[USBDPI_MAX_DATA];
};

/**
 * Set up all of the available transfer descriptors in a USB DPI context
 *
 * @param  ctx       USB DPI context
 */
void usb_transfer_setup(usbdpi_ctx_t *ctx);

/**
 * Allocate and initialise a transfer descriptor
 *
 * @param  ctx       USB DPI context
 */
usbdpi_transfer_t *transfer_alloc(usbdpi_ctx_t *ctx);

/**
 * Free a transfer descriptor and return it to the pool
 *
 * @param  ctx       USB DPI context
 * @param  transfer  Transfer descriptor to be released
 */
void transfer_release(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer);

/**
 * Initialise a transfer descriptor for use
 *
 * @param  transfer  Transfer descriptor to be initialised
 */
void transfer_init(usbdpi_transfer_t *transfer);

/**
 * Prepare and send a 'Start Of Frame' transfer descriptor
 *
 * @param  ctx       USB DPI context
 * @param  transfer  Transfer descriptor
 * @param  frame     Frame number to be sent
 */
void transfer_frame_start(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                          unsigned frame);

/**
 * Append a token packet to a transfer descriptor that is under construction
 *
 * @param  transfer  Transfer descriptor
 * @param  pid       Packet IDentifier of token packet
 * @param  device    Device address of recipient
 * @param  endpoint  Endpoint number of recipient
 */
void transfer_token(usbdpi_transfer_t *transfer, uint8_t pid, uint8_t device,
                    uint8_t endpoint);

/**
 * Append a data stage to the given transfer descriptor, using the specified PID
 * (DATA0|DATA1) and checking that there is sufficient space available
 * (est_size)
 *
 * @param  transfer  Transfer descriptor under construction
 * @param  pid       Packet IDentifier of data packet
 * @param  est_size  Estimated size of data if known (or 0)
 */
uint8_t *transfer_data_start(usbdpi_transfer_t *transfer, uint8_t pid,
                             unsigned est_size);

/**
 * Conclude a data stage within a transfer, calculating and appending the CRC16
 * of the data field
 *
 * @param  transfer  Transfer descriptor under construction
 * @param  dp        Pointer beyond the data field within the transfer
 */
void transfer_data_end(usbdpi_transfer_t *transfer, uint8_t *dp);

/**
 * Prepare a transfer for transmission to the device, and get ready to transmit
 *
 * @param  ctx       USB DPI context
 * @param  transfer  Transfer descriptor to be sent to device
 */
void transfer_send(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer);

/**
 * Construct and prepare to send a Status response;
 *
 * Note: there is no requirement to call either transfer_init() or
 *       transfer_send() when using transfer_status()
 *
 * @param  ctx       USB DPI context
 * @param  transfer  Transfer descriptor to be completed and sent
 * @param  pid       Packet IDentifier of status packet
 */
void transfer_status(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                     uint8_t pid);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
