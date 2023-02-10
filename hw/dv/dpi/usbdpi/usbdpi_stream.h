// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_STREAM_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_STREAM_H_
#include <stdbool.h>
#include <stdint.h>

#include "usb_transfer.h"

// Forwards declaration of USBDPI context
typedef struct usbdpi_ctx usbdpi_ctx_t;

// Context for streaming data test (usbdev_stream_test)
typedef struct usbdpi_stream {
  /**
   * Test requires polling device for IN packets
   */
  bool retrieve;
  /**
   * Test requires attempting to send OUT packets to device
   */
  bool send;
  /**
   * Request trying of IN packets, feigning error
   */
  bool retrying;
  /**
   * Checking of received byte stream; disable iff
   * investigating IN performance
   */
  bool checking;
  /**
   * Have we received the stream signature yet?
   */
  bool sig_recvd;
  /**
   * Device endpoint from which IN packets are retrieved
   */
  uint8_t ep_in;
  /**
   * Device endpoint to which OUT packets are sent
   */
  uint8_t ep_out;
  /**
   * Device-generated LFSR; predicts data expected from usbdev_stream_test
   */
  uint8_t tst_lfsr;
  /**
   * DPI-generated LFSR-generated data, to be combined with received data
   */
  uint8_t dpi_lfsr;
  /**
   * LFSR state for p-randomized retrying of received data
   */
  uint8_t retry_lfsr;
  /**
   * Number of times (still) to retry before accepting the current data packet
   */
  uint8_t nretries;
  /***
   * Linked-list of received transfers
   */
  usbdpi_transfer_t *received;
} usbdpi_stream_t;

/**
 * Initialize streaming state for the given number of streams
 *
 * @param  ctx       USBDPI context state
 * @param  nstreams  Number of concurrent byte streams
 * @param  retrieve  Retrieve IN packets from device
 * @param  checking  Checking of received data against expected LFSR output
 * @param  retrying  Request retrying of IN packets, feigning error
 * @param  send      Attempt to send OUT packets to device
 * @return           true iff initialized successfully
 */
bool streams_init(usbdpi_ctx_t *ctx, unsigned nstreams, bool retrieve,
                  bool checking, bool retrying, bool send);

/**
 * Service streaming data (usbdev_stream_test)
 *
 * @param  ctx       USBDPI context state
 */
void streams_service(usbdpi_ctx_t *ctx);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_STREAM_H_
