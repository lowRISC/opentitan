// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <string.h>

#include "usb_utils.h"
#include "usbdpi.h"

// Set up all of the available transfer descriptors
void usb_transfer_setup(usbdpi_ctx_t *ctx) {
  usbdpi_transfer_t *next = NULL;
  int idx = (int)USBDPI_MAX_TRANSFERS;
  while (--idx >= 0) {
    ctx->transfer_pool[idx].next = next;
    next = &ctx->transfer_pool[idx];
  }
  ctx->free = next;
}

// Allocate and initialize a transfer descriptor
usbdpi_transfer_t *transfer_alloc(usbdpi_ctx_t *ctx) {
  usbdpi_transfer_t *transfer = ctx->free;
  if (transfer) {
    ctx->free = transfer->next;
    transfer_init(transfer);
  }
  return transfer;
}

// Free a transfer descriptor
void transfer_release(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer) {
  // Prepend this transfer descriptor to the list of free descriptors
  transfer->next = ctx->free;
  ctx->free = transfer;
}

// Initialize a transfer descriptor
void transfer_init(usbdpi_transfer_t *transfer) {
  // Not within a linked list
  transfer->next = NULL;

  // Initially content free
  transfer->num_bytes = 0U;
  transfer->data_start = USBDPI_NO_DATA_STAGE;
}

// Prepare and send a 'Start Of Frame' transfer descriptor
void transfer_frame_start(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                          unsigned frame) {
  // 11 bits of the frame number are used, and they are encoded in the same
  // manner as the device address and endpoint number of other packets
  transfer_token(transfer, USB_PID_SOF, frame & 0x7FU, (frame >> 7) & 15);
  transfer_send(ctx, transfer);
}

// Construct and send the setup stage of a control transfer
void transfer_setup(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                    uint8_t bmRequestType, uint8_t bRequest, uint16_t wValue,
                    uint16_t wIndex, uint16_t wLength) {
  transfer_token(transfer, USB_PID_SETUP, ctx->dev_address, ENDPOINT_ZERO);

  uint8_t *dp = transfer_data_start(transfer, USB_PID_DATA0, 8U);
  dp[0] = bmRequestType;
  dp[1] = bRequest;
  dp[2] = (uint8_t)wValue;
  dp[3] = (uint8_t)(wValue >> 8);
  dp[4] = (uint8_t)wIndex;
  dp[5] = (uint8_t)(wIndex >> 8);
  dp[6] = (uint8_t)wLength;
  dp[7] = (uint8_t)(wLength >> 8);
  transfer_data_end(transfer, dp + 8);

  // Send the transfer descriptor
  transfer_send(ctx, transfer);
  ctx->bus_state = kUsbControlSetup;
  ctx->wait = USBDPI_TIMEOUT(ctx, USBDPI_INTERVAL_SETUP_STAGE);
  ctx->hostSt = HS_WAITACK;
}

// Append a token packet to a transfer descriptor that is under construction
void transfer_token(usbdpi_transfer_t *transfer, uint8_t pid, uint8_t device,
                    uint8_t endpoint) {
  assert(device < 0x80U);
  assert(endpoint < 0x10U);

  transfer_init(transfer);

  assert(transfer->num_bytes <= sizeof(transfer->data) - 3);
  uint8_t *dp = &transfer->data[transfer->num_bytes];

  dp[0] = pid;
  dp[1] = (uint8_t)(device | (endpoint << 7));
  dp[2] =
      (uint8_t)((endpoint >> 1) | (CRC5((endpoint << 7) | device, 11) << 3));

  transfer->num_bytes += 3U;
}

// Append a data stage to the given transfer descriptor, using the specified PID
//   (DATA0|DATA1)  and checking that there is sufficient space available
//   (est_size)
uint8_t *transfer_data_start(usbdpi_transfer_t *transfer, uint8_t pid,
                             unsigned est_size) {
  // TODO - we should at this point check that we are properly compliant with
  //        DATA0|DATA1 signalling too!
  //        unless of course we are deliberately being non-compliant
  assert(pid == USB_PID_DATA0 || pid == USB_PID_DATA1);

  // If an estimated size has been speciifed, check whether there's sufficient
  // space
  unsigned data_start = transfer->num_bytes;
  if (est_size > sizeof(transfer->data) - 1U - data_start) {
    assert(!"transfer_data_start space check failed");
    return NULL;
  }

  // Retain the offset of the PID (not the data field itself) for the
  // calculation of the CRC16 and for the signalling transition (EOP) when we
  // come to send this...
  transfer->data_start = data_start;
  uint8_t *dp = &transfer->data[data_start];
  *dp++ = pid;
  transfer->num_bytes++;

  // We return a pointer to where the data stage shall be constructed, and the
  // caller shall pass the advanced pointer to tranfer_data_end() to ensure
  // correct completion of the data stage
  return dp;
}

// Conclude a data stage within a transfer, calculating and appending the CRC16
// of the data field
void transfer_data_end(usbdpi_transfer_t *transfer, uint8_t *dp) {
  assert(transfer->data_start != USBDPI_NO_DATA_STAGE);
  assert(dp >= transfer->data);

  // Check that we still have space to append the CRC16
  assert(dp < transfer->data + sizeof(transfer->data) - 2);

  // Note: historically the datastart field has pointed to the PID rather than
  //       the data field itself
  const uint8_t *data_field = &transfer->data[transfer->data_start + 1U];
  uint32_t crc = CRC16(data_field, dp - data_field);
  dp[0] = (uint8_t)crc;
  dp[1] = (uint8_t)(crc >> 8);

  // Update the count of bytes in the transfer
  transfer->num_bytes = (dp + 2) - transfer->data;
}

// Append some data to a transfer description
bool transfer_append(usbdpi_transfer_t *transfer, const uint8_t *dp, size_t n) {
  unsigned num_bytes = transfer->num_bytes;

  // Check that we still have space to append this data
  if (sizeof(transfer->data) - num_bytes < n) {
    return false;
  }
  memcpy(&transfer->data[num_bytes], dp, n);
  transfer->num_bytes = num_bytes + n;
  return true;
}

// Prepare a transfer for transmission to the device, and get ready to transmit
void transfer_send(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer) {
  // Validate the transfer properties
  assert(transfer->num_bytes > 0U &&
         transfer->num_bytes <= sizeof(transfer->data));

  // Set this as the current in-progress transfer, checking that we're not
  // losing track of a buffer by doing so.
  assert(!ctx->sending || ctx->sending == transfer);
  ctx->sending = transfer;

  // Prepare for transmission of the first byte, following the implicit SYNC
  ctx->state = ST_SYNC;
  ctx->byte = 0;
  ctx->bit = 1;
}

// Construct and prepare to send a Status response;
// Note: there is no requirement to call either transfer_init() or
//       transfer_send() when using transfer_status()
void transfer_status(usbdpi_ctx_t *ctx, usbdpi_transfer_t *transfer,
                     uint8_t pid) {
  // The single byte Status stage carries just the PID
  transfer->num_bytes = 1U;
  transfer->data[0] = pid;

  transfer->data_start = USBDPI_NO_DATA_STAGE;

  // Set this as the current in-progress transfer, checking that we're not
  // losing track of a buffer by doing so.
  assert(!ctx->sending || ctx->sending == transfer);
  ctx->sending = transfer;

  // Prepare for transmission of the first byte, following the implicit SYNC
  ctx->state = ST_SYNC;
  ctx->byte = 0;
  ctx->bit = 1;
}

// Diagnostic utility function to dump out the contents of a transfer descriptor
void transfer_dump(const usbdpi_transfer_t *transfer, FILE *out) {
  fprintf(out, "[usbdpi] Transfer descriptor at %p\n", transfer);
  fprintf(out, "[usbdpi] num_bytes 0x%x data_start 0x%x\n", transfer->num_bytes,
          transfer->data_start);
  dump_bytes(out, "[usbdpi] ", transfer->data, transfer->num_bytes, 0U);
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern uint8_t *transfer_data_field(usbdpi_transfer_t *transfer);
extern uint8_t transfer_data_pid(usbdpi_transfer_t *transfer);
extern uint32_t transfer_length(const usbdpi_transfer_t *transfer);
