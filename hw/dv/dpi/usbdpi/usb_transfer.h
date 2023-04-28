// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

// USBDEV IP block supports up to 64-bytes/packet
#ifndef USBDEV_MAX_PACKET_SIZE
#define USBDEV_MAX_PACKET_SIZE 64U
#endif

// Maximal length of a byte sequence to be transmitted/receive without
// interruption or pause (Start Of Frame, Setup packet, OUT Data packet,
// all back-to-back)
#define USBDPI_MAX_DATA                          \
  (3U +                              /* SOF */   \
   3U +                              /* SETUP */ \
   1U + USBDEV_MAX_PACKET_SIZE + 2U) /* DATA PID, field, CRC16 */

// Special value that denotes that this transfer does not include a data stage
#define USBDPI_NO_DATA_STAGE ((uint8_t)~0U)

// USB Transfer Types (Standard Endpoint Descriptor)
#define USB_TRANSFER_TYPE_CONTROL 0U
#define USB_TRANSFER_TYPE_ISOCHRONOUS 1U
#define USB_TRANSFER_TYPE_BULK 2U
#define USB_TRANSFER_TYPE_INTERRUPT 3U

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

/**
 * Set up all of the available transfer descriptors in a USB DPI context
 *
 * @param  ctx       USB DPI context
 */
void usb_transfer_setup(usbdpi_ctx_t *ctx);

/**
 * Allocate and initialize a transfer descriptor
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
 * Initialize a transfer descriptor for use
 *
 * @param  transfer  Transfer descriptor to be initialized
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
 * Construct and send the setup stage of a control transfer
 *
 * @param  ctx           USB DPI context
 * @param  transfer      Transfer descriptor
 * @param  bmRequestType Characteristics of USB device request
 * @param  bRequest      Specific device request
 * @param  wValue        Word-sized field that varies according to the request
 * @param  WIndex        Typically used to pass an index or offset
 * @param  wLength       Number of bytes to transfer if there is a Data stage
 */
void transfer_setup(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                    uint8_t bmRequestType, uint8_t bRequest, uint16_t wValue,
                    uint16_t wIndex, uint16_t wLength);

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
 * Return access to the data field of a transfer descriptor
 *
 * @param  transfer  Transfer descriptor
 * @return           Pointer to the start of the data field or NULL
 */
inline uint8_t *transfer_data_field(usbdpi_transfer_t *transfer) {
  assert(transfer);
  if (transfer->data_start != USBDPI_NO_DATA_STAGE &&
      transfer->data_start + 1U < transfer->num_bytes) {
    return &transfer->data[transfer->data_start + 1U];
  }
  return NULL;
}

/**
 * Return DATAx PID of the data field of a transfer descriptor
 *
 * @param  transfer  Transfer descriptor
 * @return           USB_PID_DATA0|1
 */
inline uint8_t transfer_data_pid(usbdpi_transfer_t *transfer) {
  assert(transfer);
  assert(transfer->data_start != USBDPI_NO_DATA_STAGE &&
         transfer->data_start + 1U < transfer->num_bytes);
  return transfer->data[transfer->data_start];
}

/**
 * Append some data to a transfer description
 *
 * @param  transfer  Transfer descriptor under construction
 * @param  dp        Pointer to data bytes to be appended
 * @param  n         Number of bytes
 * @return           true iff appended successfully
 */
bool transfer_append(usbdpi_transfer_t *transfer, const uint8_t *dp, size_t n);

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

/**
 * Returns the total number of bytes to be transferred
 *
 * @param  transfer  Transfer descriptor
 * @return           Number of bytes
 */

inline uint32_t transfer_length(const usbdpi_transfer_t *transfer) {
  return transfer->num_bytes;
}

/**
 * Diagnostic utility function to dump out the contents of a transfer descriptor
 *
 * @param  transfer  Transfer descriptor
 * @param  out       Stream to receive diagnostic output
 */
void transfer_dump(const usbdpi_transfer_t *transfer, FILE *out);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_TRANSFER_H_
