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
// interruption or pause
//   (Start Of Frame, Setup packet, OUT Data packet and End Of Frame all
//   back-to-back?)
#define USBDPI_MAX_DATA (3U + 3U + 1U + USBDEV_MAX_PACKET_SIZE + 2U + 1U)

/**
 * Forwards reference to usbpdi state context
 */
typedef struct usbdpi_ctx usbdpi_ctx_t;

/**
 * Description of a transfer over the USB
 *
 * A control transfer
 *    Setup stage - [ Data stage ] - Status stage
 * A data transfer
 *    Setup stage - Data stage - [ Status stage ]
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

// Set up all of the available transfer descriptors
void usb_transfer_setup(usbdpi_ctx_t *ctx);

// Allocate and initialise a transfer descriptor
usbdpi_transfer_t *transfer_alloc(usbdpi_ctx_t *ctx);
// Free a transfer descriptor
void transfer_release(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer);
// Initialise a transfer descriptor
void transfer_init(usbdpi_transfer_t *transfer);
// Prepare and send a 'Start Of Frame' transfer descriptor
void transfer_frame_start(usbdpi_ctx_t *ctx, usbdpi_transfer_t *tr,
                          unsigned frame);
// Append a token packet to a transfer descriptor that is under construction
void transfer_token(usbdpi_transfer_t *transfer, uint8_t pid, uint8_t device,
                    uint8_t endpoint);
// Append a data stage to the given transfer descriptor, using the specified PID
// (DATA0|DATA1)
//   and checking that there is sufficient space available (est_size)
uint8_t *transfer_data_start(usbdpi_transfer_t *transfer, uint8_t pid,
                             unsigned est_size);
// Conclude a data stage within a transfer, calculating and appending the CRC16
// of the data field
void transfer_data_end(usbdpi_transfer_t *transfer, uint8_t *dp);
// Prepare a transfer for transmission to the device, and get ready to transmit
void transfer_send(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer);
// Construct and prepare to send a Status response;
// Note: there is no requirement to call either transfer_init() or
// transfer_send()
//       when using transfer_status()
void transfer_status(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                     uint8_t pid);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
