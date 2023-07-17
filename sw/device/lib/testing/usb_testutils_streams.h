// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_STREAMS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_STREAMS_H_
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/usb_testutils.h"

// Maximum number of concurrent streams
#ifndef USBUTILS_STREAMS_MAX
#ifdef USBDEV_NUM_ENDPOINTS
// Endpoint zero implements the default control pipe
#define USBUTILS_STREAMS_MAX (USBDEV_NUM_ENDPOINTS - 1U)
#else
#define USBUTILS_STREAMS_MAX 11U
#endif
#endif

// Maximum number of buffer simultaneously awaiting transmission
// (we must leave some available for packet reception)
#ifndef USBUTILS_STREAMS_TXBUF_MAX
#define USBUTILS_STREAMS_TXBUF_MAX 24U
#endif

// Stream signature words
#define USBDEV_STREAM_SIGNATURE_HEAD 0x579EA01AU
#define USBDEV_STREAM_SIGNATURE_TAIL 0x160AE975U

// Seed numbers for the LFSR generators in each transfer direction for
// the given stream number
#define USBTST_LFSR_SEED(s) (uint8_t)(0x10U + (s)*7U)
#define USBDPI_LFSR_SEED(s) (uint8_t)(0x9BU - (s)*7U)

// Buffer size randomization
#define BUFSZ_LFSR_SEED(s) (uint8_t)(0x17U + (s)*7U)

// Simple LFSR for 8-bit sequences
/// Note: zero is an isolated state that shall be avoided
#define LFSR_ADVANCE(lfsr)     \
  (uint8_t)(                   \
      (uint8_t)((lfsr) << 1) ^ \
      ((((lfsr) >> 1) ^ ((lfsr) >> 2) ^ ((lfsr) >> 3) ^ ((lfsr) >> 7)) & 1U))

// Test/stream flags
typedef enum {
  /**
   * Host shall retrieve IN data from the device for this stream
   */
  kUsbdevStreamFlagRetrieve = 0x10U,
  /**
   * Host shall check that IN data matches as expected
   */
  kUsbdevStreamFlagCheck = 0x20U,
  /**
   * DPI model (or Host) shall retry IN data fetches, where possible
   */
  kUsbdevStreamFlagRetry = 0x40U,
  /**
   * Host shall send OUT data to the device for this stream
   */
  kUsbdevStreamFlagSend = 0x80U,
  /**
   * Transmit only maximal length packets
   */
  kUsbdevStreamFlagMaxPackets = 0x100U,
} usbdev_stream_flags_t;

// Forward declaration to context state
typedef struct usb_testutils_streams_ctx usb_testutils_streams_ctx_t;

/**
 * Stream signature
 * Note: this needs to be transferred over a byte stream
 */
typedef struct __attribute__((packed)) usbdev_stream_sig {
  /**
   * Head signature word
   */
  uint32_t head_sig;
  /**
   * Initial value of LFSR
   * Note: for Isochronous Transfers, this is the initial value of the sender's
   *       LFSR for _this packet_
   */
  uint8_t init_lfsr;
  /**
   * Stream number (bits 3:0) and flags (bits 7:4)
   */
  uint8_t stream;
  /**
   * Sequence number, low part; for non-Isochronous streams this will always be
   * zero because a signature is used only at the start of the data stream.
   */
  uint8_t seq_lo;
  /**
   * Sequence number, high part; for non-Isochronous streams this will always be
   * zero because a signature is used only at the start of the data stream.
   */
  uint8_t seq_hi;
  /**
   * Number of bytes to be transferred; for Isochronous streams this
   * is the count of remaining bytes and it wraps when reaching zero
   */
  uint32_t num_bytes;
  /**
   * Tail signature word
   */
  uint32_t tail_sig;
} usbdev_stream_sig_t;

// Sanity check because the host-side code relies upon the same structure
static_assert(sizeof(usbdev_stream_sig_t) == 0x10U,
              "Host-side code relies upon signature structure");

/**
 * Transmission state.
 */
typedef struct usbdev_stream_tx {
  /**
   * Is a signature required at the start of the next packet?
   */
  bool sig_required;
  /**
   * Transmission Sequence Number (for Isochronous streams)
   */
  uint16_t seq;
  /**
   * Transmission Linear Feedback Shift Register (for PRND data generation)
   */
  uint8_t lfsr;
  /**
   * Total number of bytes presented to the USB device for transmission
   */
  uint32_t bytes;
  /**
   * Transmission-side LFSR for selection of buffer size
   */
  uint8_t buf_size;
} usbdev_stream_tx_t;

/**
 * Context state for a single stream
 *
 * Note: this state information is stored/loaded as-is over suspend/resume
 *       operations.
 */
typedef struct usbdev_stream {
  /**
   * Stream IDentifier
   */
  uint8_t id;
  /**
   * USB transfer type
   */
  usb_testutils_transfer_type_t xfr_type;
  /**
   * USB device endpoint being used for data transmission
   */
  uint8_t tx_ep;
  /**
   * Current transmission state.
   */
  usbdev_stream_tx_t tx;
  /**
   * USB device endpoint being used for data reception
   */
  uint8_t rx_ep;
  /**
   * Reception Sequence Number (for Isochronous streams)
   */
  uint16_t rx_seq;
  /**
   * Reception-side LFSR state (mirrors USBDPI generation of PRND data)
   */
  uint8_t rx_lfsr;
  /**
   * Reception-side shadow of transmission LFSR
   */
  uint8_t rxtx_lfsr;
  /**
   * Total number of bytes received from the USB device
   */
  uint32_t rx_bytes;
  /**
   * Reception-side LFSR for determination of expected buffer size
   * (for Isochronous streams where packets may be dropped)
   */
  uint8_t rx_buf_size;
  /**
   * Size of transfer in bytes
   */
  uint32_t transfer_bytes;
  /**
   * Stream flags
   */
  usbdev_stream_flags_t flags;
  /**
   * Are we sending data?
   */
  bool sending;
  /**
   * Are we generating a valid byte sequence?
   */
  bool generating;
  /**
   * Specify whether to perform verbose logging, for visibility
   *   (Note that this substantially alters the timing of interactions with the
   * DPI model and will increase the simulation time)
   */
  bool verbose;
} usbdev_stream_t;

/**
 * Context state for callback function; callback is stream-specific but also
 * needs to locate the enclosing streaming context.
 */
typedef struct {
  /**
   * Pointer to the enclosing streaming context; callback functions receive
   * only per-stream pointer
   */
  usb_testutils_streams_ctx_t *ctx;
  /**
   * Pointer to the stream itself.
   */
  usbdev_stream_t *s;
} usbdev_stream_cb_t;

/**
 * Context state for streaming test
 */
struct usb_testutils_streams_ctx {
  /**
   * Context pointer
   */
  usb_testutils_ctx_t *usbdev;
  /**
   * Number of streams in use
   */
  uint8_t nstreams;
  /**
   * State information for each of the test streams
   */
  usbdev_stream_t streams[USBUTILS_STREAMS_MAX];
  /**
   * Callback information for each of the test streamms
   */
  usbdev_stream_cb_t cb[USBUTILS_STREAMS_MAX];
  /**
   * Per-endpoint limits on the number of buffers that may be queued for
   * transmission
   */
  uint8_t tx_bufs_limit[USBDEV_NUM_ENDPOINTS];
  /**
   * Per-endpoint counts of completed buffers queued for transmission
   */
  uint8_t tx_bufs_queued[USBDEV_NUM_ENDPOINTS];
  /**
   * Total number of completed buffers
   */
  uint8_t tx_queued_total;
  /**
   * Buffers that have been filled but cannot yet be presented for transmission
   */
  // 12 X 24 X 4 (or 8?)( BYTES... could perhaps simplify this at some point
  dif_usbdev_buffer_t tx_bufs[USBDEV_NUM_ENDPOINTS][USBUTILS_STREAMS_TXBUF_MAX];
};

/**
 * Initialize a number of concurrent streams with the same properties;
 * this set of streams is assigned endpoints from endpoint 1 upwards, in order.
 *
 * @param  ctx       Context state for streaming test
 * @param  nstreams  Number of streams
 * @param  xfr_types Transfer types to be used for the individual streams
 * @param  num_bytes Number of bytes to be transferred by each stream
 * @param  flags     Stream/test flags to be used for each stream
 * @param  verbose   Whether to perform verbose logging for each stream
 * @return The result status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_streams_init(usb_testutils_streams_ctx_t *ctx,
                                    unsigned nstreams,
                                    usb_testutils_transfer_type_t xfr_types[],
                                    uint32_t num_bytes,
                                    usbdev_stream_flags_t flags, bool verbose);

/**
 * Service all streams, preparing and/or sending any data that we can, as well
 * as handling received data.
 *
 * Note: this calls usb_testutils_poll() internally to keep that layer alive
 *       and handling packet reception.
 *
 * @param  ctx       Context state for streaming test
 * @return The result status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_streams_service(usb_testutils_streams_ctx_t *ctx);

/**
 * Returns an indication of whether all streams have completed their data
 * transfers.
 *
 * @param  ctx       Context state for streaming test
 */
OT_WARN_UNUSED_RESULT
bool usb_testutils_streams_completed(const usb_testutils_streams_ctx_t *ctx);

/**
 * Initialize a stream, preparing it for use.
 *
 * @param  ctx       Context state for streaming test
 * @param  id        Stream identifier (0-based)
 * @param  xfr_type  Transfer type to be usd for this stream
 * @param  ep_in     Endpoint to be used for IN traffic (to host)
 * @param  ep_out    Endpoint to be used for OUT traffic (from host)
 * @param  num_bytes Number of bytes to be transferred by stream
 * @param  flags     Stream/test flags
 * @param  verbose   Whether to perform verbose logging for this stream
 * @return The result status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_stream_init(usb_testutils_streams_ctx_t *ctx, uint8_t id,
                                   usb_testutils_transfer_type_t xfr_type,
                                   uint8_t ep_in, uint8_t ep_out,
                                   uint32_t num_bytes,
                                   usbdev_stream_flags_t flags, bool verbose);

/**
 * Specify the number of already-initialized streams, and apportion the
 * available tx buffers among them. To be called after usb_testutils_stream_init
 *
 * @param  ctx       Context state for streaming test.
 * @param  nstreams  Number of streams.
 * @return           Success or otherwise of the request.
 */
bool usb_testutils_streams_count_set(usb_testutils_streams_ctx_t *ctx,
                                     unsigned nstreams);

/**
 * Service the given stream, preparing and/or sending any data that we can.
 *
 * Note: the caller must invoke usb_testutils_poll() itself in order to ensure
 *       that packet reception continues to occur.
 *
 * @param  ctx       Context state for streaming test
 * @param  id        Stream identifier (0-based)
 * @return The result status of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_stream_service(usb_testutils_streams_ctx_t *ctx,
                                      uint8_t id);

/**
 * Returns an indication of whether a stream has completed its data transfer.
 *
 * @param  ctx       Context state for streaming test
 * @param  id        Stream identifier (0-based)
 */
OT_WARN_UNUSED_RESULT
bool usb_testutils_stream_completed(const usb_testutils_streams_ctx_t *ctx,
                                    uint8_t id);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_STREAMS_H_
