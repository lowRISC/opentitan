// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/usb_logging.h"

#include <ctype.h>

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/usb_testutils.h"
#include "sw/device/lib/testing/usb_testutils_controlep.h"

#define MODULE_ID MAKE_MODULE_ID('u', 's', 'l')

enum {
  // Size of each logging buffer; data is collected in a buffer until the buffer
  // is full (or the periodic flush occurs) and is then transmitted as a single
  // transfer at higher throughput.
  kUSBLogBufferSize = 0x800u,

  // Total number of logging buffers to be shared among all active streams.
  kUSBLogNumBuffers = 8u,

  // Maximum delay before logging data is flushed upstream to the host;
  // microseconds.
  kUSBLogFlushInterval = 500u * 1000u,
};

// Maximum length of the configuration descriptor.
enum {
  kCfgDscrLenMax =
      (USB_CFG_DSCR_LEN +
       kUSBLogMaxStreams * (USB_INTERFACE_DSCR_LEN + 1u * USB_EP_DSCR_LEN)),
};

// Forward reference required for linked list.
typedef struct usb_logging_buf usb_logging_buf_t;

// USB logging buffer description.
struct usb_logging_buf {
  /**
   * Link to the next buffer for this stream, or the next free buffer.
   */
  usb_logging_buf_t *next;
  /**
   * Number of used bytes; index at which next write shall occur.
   */
  uint16_t bytes_used;
  /**
   * Data buffer holding logging data.
   */
  uint8_t data[kUSBLogBufferSize];
};

// Forwards reference to logging context.
typedef struct usb_logging_ctx usb_logging_ctx_t;

// Per-stream state information.
typedef struct usb_logging_stream {
  /**
   * Context pointer; for use within callback handler.
   */
  usb_logging_ctx_t *ctx;
  /**
   * Reliable delivery required?
   */
  bool reliable;
  /**
   * Remapping for non-printable characters required?
   */
  bool remap;
  /**
   * The USB device endpoint that we're using.
   */
  uint8_t ep;
  /**
   * Currently sending a buffer?
   */
  bool sending;
  /**
   * The oldest logging buffer filled by this stream; this is either being
   * sent (`sending` == true) or shall be the next to send. May be NULL iff
   * this stream has no completed buffers to send.
   */
  usb_logging_buf_t *send_buf;
  /**
   * Time at which the most recently-populated buffer should be sent to the
   * host; prevent log data being retained indefinitely in the event of no
   * further log output.
   */
  ibex_timeout_t flush_time;
  /**
   * The current logging buffer; may be partially-filled or full (see
   * `bytes_used` field), or NULL iff this stream has no pending logging data.
   */
  usb_logging_buf_t *wr_buf;
} usb_logging_stream_t;

// USB Logging context.
struct usb_logging_ctx {
  /**
   * Access to usb_testutils layer.
   */
  usb_testutils_ctx_t *usbutils;
  /**
   * Number of logging streams.
   */
  uint8_t nstreams;
  /**
   * Linked-list of free buffers.
   */
  usb_logging_buf_t *free;
  /**
   * Per-stream state information.
   */
  usb_logging_stream_t streams[kUSBLogMaxStreams];
  /**
   * Pool of logging buffers; shared among all active streams.
   */
  usb_logging_buf_t buf[kUSBLogNumBuffers];
};

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;

// Note: for now there is a single logging context.
static usb_logging_ctx_t the_ctx;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

/**
 * Internal development logging; be careful about using this if stdout has been
 * redirected!
 */
static const bool kDevLogging = false;

/**
 * Character map, used to ensure that non-printable characters are dropped;
 * isprint() available so this assumes ASCII and drops the control characters
 * that could could issues with inappropriate terminal settings at the host.
 */
static const uint32_t kCtrlChars =
    ((uint32_t)1u << '\t') | ((uint32_t)1u << '\n') | ((uint32_t)1u << '\r');
static const uint32_t kMap[0x100u / 0x20u] = {
    // suppress control characters and ASCII 127 (Delete)
    kCtrlChars, ~0u, ~0u, 0x7fffffffu,
    // top-bit set characters are harmless; propagate them unchanged.
    ~0u, ~0u, ~0u, ~0u};

// Our stdout function
static size_t usb_log(void *data, const char *buf, size_t len);

/**
 * Configuration values for USB.
 */
static uint8_t config_descriptors[kCfgDscrLenMax];

// Since isprint() is unavailable, use a simple bitmap to test whether it is
// safe to transmit the given ASCII character unmodified.
static bool isprintable(uint8_t ch) {
  return ((kMap[ch >> 5] >> (ch & 0x1fu)) & 1u) != 0u;
}

// Place all buffers into the free list
static void free_list_init(usb_logging_ctx_t *ctx) {
  usb_logging_buf_t *prev = NULL;  // End of list.
  unsigned idx = kUSBLogNumBuffers;
  // Order them such that the first buffer is initially at the head.
  while (idx-- > 0u) {
    ctx->buf[idx].next = prev;
    prev = &ctx->buf[idx];
  }
  ctx->free = ctx->buf;
}

// Attempt to claim a buffer from the free list.
static inline usb_logging_buf_t *buffer_claim(usb_logging_ctx_t *ctx) {
  usb_logging_buf_t *buf = ctx->free;
  if (buf) {
    ctx->free = buf->next;
    buf->next = NULL;
    buf->bytes_used = 0u;
  }
  return buf;
}

// Return a buffer to the free list.
static inline void buffer_release(usb_logging_ctx_t *ctx,
                                  usb_logging_buf_t *buf) {
  buf->next = ctx->free;
  ctx->free = buf;
}

static status_t buffer_send(usb_logging_ctx_t *ctx, usb_logging_stream_t *s) {
  TRY_CHECK(ctx && s && s->send_buf);

  const uint8_t *data = s->send_buf->data;
  uint16_t len = s->send_buf->bytes_used;

  if (kDevLogging) {
    LOG_INFO("sending %p %p %u\n", ctx, data, len);
  }

  TRY(usb_testutils_transfer_send(ctx->usbutils, s->ep, data, len,
                                  kUsbTestutilsXfrDoubleBuffered));
  // Have at least started to send the buffer...
  s->sending = true;
  return OK_STATUS();
}

static status_t buffer_completed(usb_logging_ctx_t *ctx,
                                 usb_logging_stream_t *s) {
  TRY_CHECK(s->wr_buf);

  // Make the buffer available for sending.
  usb_logging_buf_t **prev = &s->send_buf;
  while (*prev) {
    prev = &(*prev)->next;
  }
  *prev = s->wr_buf;
  s->wr_buf = NULL;

  // Attempt to send.
  status_t res = OK_STATUS();
  if (!s->sending) {
    res = buffer_send(ctx, s);
  }
  return res;
}

// Attempt to close a logging stream, flushing any remaining data upstream to
// the host if required.
// Returns true iff the stream has closed successfully; otherwise there is still
// work to be done.
static inline bool stream_close(usb_logging_ctx_t *ctx,
                                usb_logging_stream_t *s) {
  if (s->wr_buf) {
    buffer_completed(ctx, s);
  }
  return !s->send_buf;
}

// A buffer of logging data has been received by the host; we may try to
// send another buffer if one is available.
static status_t tx_done(void *s_v, usb_testutils_xfr_result_t result) {
  usb_logging_stream_t *s = (usb_logging_stream_t *)s_v;
  usb_logging_ctx_t *ctx = s->ctx;

  s->sending = false;

  // Return this buffer to the free list.
  usb_logging_buf_t *buf = s->send_buf;
  TRY_CHECK(buf != NULL);
  s->send_buf = buf->next;
  buffer_release(ctx, buf);

  // Send the next, if there is one
  if (s->send_buf) {
    TRY(buffer_send(ctx, s));
  }
  return OK_STATUS();
}

// Callback function from the usb_testutils layer; presently this is called
// every 16ms, provided that usb_testutils_poll is being called often.
static status_t tx_flush(void *s_v) {
  usb_logging_stream_t *s = (usb_logging_stream_t *)s_v;
  usb_logging_ctx_t *ctx = s->ctx;

  // We use this to prevent incomplete buffers of log data sitting here
  // indefinitely and not reaching the host.
  usb_logging_buf_t *buf = s->wr_buf;
  if (buf && ibex_timeout_check(&s->flush_time)) {
    if (buf->bytes_used > 0u) {
      // Send everything that we have thus far collected in this buffer,
      buffer_completed(ctx, s);
    }
    // Earliest time at which we shall again attempt flushing of log data on
    // this stream.
    s->flush_time = ibex_timeout_init(kUSBLogFlushInterval);
  }

  return OK_STATUS();
}

// Internal function for all USB logging.
static status_t usb_logging_send(usb_logging_ctx_t *ctx,
                                 usb_logging_stream_t *s, const uint8_t *data,
                                 size_t len) {
  do {
    // We must poll the testutils layer to keep things going...do this even if
    // we've somehow been asked to log zero bytes of data.
    TRY(usb_testutils_poll(ctx->usbutils));

    // Try to ensure that we have a logging buffer.
    if (!s->wr_buf) {
      s->wr_buf = buffer_claim(ctx);
    }
    if (s->wr_buf) {
      usb_logging_buf_t *buf = s->wr_buf;

      // Add as much as we can to the current logging buffer.
      size_t chunk = kUSBLogBufferSize - buf->bytes_used;
      if (chunk > len) {
        chunk = len;
      }
      if (s->remap) {
        // Remap non-printable characters, to avoid issues with accidentally
        // stimulated software flow control (XON/XOFF) at the host.
        uint8_t *dp = &buf->data[buf->bytes_used];
        for (size_t i = 0u; i < chunk; ++i) {
          dp[i] = isprintable(data[i]) ? data[i] : '.';
        }
      } else {
        memcpy(&buf->data[buf->bytes_used], data, chunk);
      }
      // Advance beyond the chunk that we've handled.
      data += chunk;
      len -= chunk;

      // Initialize timeout at the point of starting to fill a buffer, since it
      // will be sent as a complete unit.
      if (!buf->bytes_used) {
        s->flush_time = ibex_timeout_init(kUSBLogFlushInterval);
      }

      // Is this packet buffer now ready to be sent?
      buf->bytes_used += chunk;
      if (buf->bytes_used >= kUSBLogBufferSize) {
        buffer_completed(ctx, s);
      }
    } else if (!s->reliable) {
      // Blocked awaiting another buffer; drop logging data.
      break;
    }
  } while (len);  // Any more to send?

  return OK_STATUS();
}

// Interface for known-length (binary) data.
status_t usb_logging_data(uint8_t s, const uint8_t *data, size_t len) {
  usb_logging_ctx_t *ctx = &the_ctx;
  TRY_CHECK(s < ctx->nstreams);

  return usb_logging_send(ctx, &ctx->streams[s], data, len);
}

// Interface for ASCIIZ text message.
status_t usb_logging_text(uint8_t s, const char *text) {
  usb_logging_ctx_t *ctx = &the_ctx;
  TRY_CHECK(s < ctx->nstreams);
  TRY_CHECK(text);

  // Note: no strlen() available.
  uint32_t len = (uint32_t)((char *)memchr(text, 0, SIZE_MAX) - text);
  return usb_logging_send(ctx, &ctx->streams[s], (const uint8_t *)text, len);
}

// stdout redirection.
static size_t usb_log(void *data, const char *buf, size_t len) {
  usb_logging_stream_t *s = (usb_logging_stream_t *)data;
  if (s) {
    usb_logging_ctx_t *ctx = s->ctx;
    status_t res = usb_logging_send(ctx, s, (uint8_t *)buf, len);
    if (status_ok(res)) {
      return len;
    }
  }
  return 0u;
}

status_t usb_logging_enable(void) {
  usb_logging_ctx_t *ctx = &the_ctx;

  // Set up a single reliable logging stream; if `ctx->usbutils` is non-zero
  // then the usb_testutils has already been initialized.
  // Should be no need to incur the performance hit of remapping characters,
  // if base_printf/usage is well-behaved.
  TRY(usb_logging_init(ctx->usbutils, 1u, 1u, 1u, false));

  // Construct the descriptor of our USB sink function for stdout.
  buffer_sink_t sink;
  sink.data = &ctx->streams[0];
  sink.sink = usb_log;
  // Redirect stdout to us
  base_set_stdout(sink);

  return OK_STATUS();
}

status_t usb_logging_init(usb_testutils_ctx_t *usbutils, uint8_t ep_first,
                          uint8_t nstreams, uint32_t reliable, bool remap) {
  usb_logging_ctx_t *ctx = &the_ctx;

  // Validate input arguments.
  TRY_CHECK(nstreams > 0u && nstreams <= kUSBLogMaxStreams);

  // Set up the software layers, if required.
  if (usbutils) {
    // usb_testutils layer already initialized, so an endpoint number must be
    // supplied.
    ctx->usbutils = usbutils;
    TRY_CHECK(ep_first >= 1u && USBDEV_NUM_ENDPOINTS >= ep_first + nstreams);
  } else {
    // Pointers to context for lower software layers.
    ctx->usbutils = &usbdev;
    ep_first = 1u;

    TRY(dif_pinmux_init(
        mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
    pinmux_testutils_init(&pinmux);
    TRY(dif_pinmux_input_select(&pinmux,
                                kTopEarlgreyPinmuxPeripheralInUsbdevSense,
                                kTopEarlgreyPinmuxInselIoc7));

    // Total length of the configuration descriptor; validate caller buffer.
    size_t cfg_len = USB_CFG_DSCR_LEN +
                     nstreams * (USB_INTERFACE_DSCR_LEN + USB_EP_DSCR_LEN);
    TRY_CHECK(cfg_len <= sizeof(config_descriptors));

    // Configuration Descriptor header.
    uint8_t *cfg = config_descriptors;
    uint8_t head[USB_CFG_DSCR_LEN] = {
        USB_CFG_DSCR_HEAD((uint16_t)cfg_len, (uint8_t)nstreams)};
    memcpy(cfg, head, USB_CFG_DSCR_LEN);
    cfg += USB_CFG_DSCR_LEN;

    // Followed by programmatically-generated list of interface descriptors.
    for (uint8_t id = 0U; id < nstreams; ++id) {
      uint8_t ep_in = ep_first + id;
      // Description of a single interface.
      uint8_t int_dscr[USB_INTERFACE_DSCR_LEN + USB_EP_DSCR_LEN] = {
          VEND_INTERFACE_DSCR(id, 1, 0x50, 1),
          // Declare only an IN endpoint because we don't require OUT traffic
          // and any character echo would just be wasting bus bandwidth.
          USB_EP_DSCR(1, ep_in, (uint8_t)kUsbTransferTypeBulk,
                      USBDEV_MAX_PACKET_SIZE, 0),
      };

      // Append interface descriptor to the configuration descriptor.
      memcpy(cfg, int_dscr, sizeof(int_dscr));
      cfg += sizeof(int_dscr);
    }

    // Call `usbdev_init` here so that DPI will not start until the
    // simulation has finished all of the printing, which takes a while
    // if `--trace` was passed in.
    TRY(usb_testutils_init(ctx->usbutils, /*pinflip=*/false,
                           /*en_diff_rcvr=*/true,
                           /*tx_use_d_se0=*/false));
    TRY(usb_testutils_controlep_init(&usbdev_control, ctx->usbutils, 0,
                                     config_descriptors, cfg_len, NULL,
                                     0u));  // No need for test descriptor.
  }

  // Initialize list of free buffers.
  free_list_init(ctx);

  // Initialize the time of the next flush on each stream; stagger them to
  // avoid all flush operations coinciding and producing traffic that is more
  // bursty.
  const uint32_t flush_inc = kUSBLogFlushInterval / nstreams;
  uint32_t interval_us = kUSBLogFlushInterval / 2u;

  for (uint8_t s = 0u; s < nstreams; ++s) {
    usb_logging_stream_t *stream = &ctx->streams[s];
    // Context pointer, for use within callback handler.
    stream->ctx = ctx;
    // Reliable delivery required?
    stream->reliable = (((reliable >> s) & 1u) != 0u);
    // Remapping required?
    stream->remap = remap;
    // Endpoint(s) to be used.
    // Note: this could be modified to permit concurrent operation with other
    // interfaces.
    stream->ep = 1u + s;
    // Sending state; nothing to send or being sent.
    stream->sending = false;
    stream->send_buf = NULL;
    // Earliest time of next flush attempt.
    stream->flush_time = ibex_timeout_init(interval_us);
    interval_us += flush_inc;
    // Writing state; no buffer initially.
    stream->wr_buf = NULL;

    TRY(usb_testutils_in_endpoint_setup(ctx->usbutils, stream->ep,
                                        kUsbTransferTypeBulk, stream, tx_done,
                                        tx_flush, NULL));
  }

  if (!usbutils) {
    // Proceed only when the device has been configured; this allows host-side
    // software to establish communication.
    const uint32_t kTimeoutUsecs = 30 * 1000000;
    ibex_timeout_t timeout = ibex_timeout_init(kTimeoutUsecs);
    while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured &&
           !ibex_timeout_check(&timeout)) {
      TRY(usb_testutils_poll(ctx->usbutils));
    }
    if (usbdev_control.device_state != kUsbTestutilsDeviceConfigured) {
      // Don't wait indefinitely because there may be no usable connection.
      return UNAVAILABLE();
    }
  }

  // Remember the stream count, now that everything is configured.
  ctx->nstreams = nstreams;

  return OK_STATUS();
}

status_t usb_logging_fin(bool wait, bool disconnect) {
  usb_logging_ctx_t *ctx = &the_ctx;

  // Wait for captured logging traffic to be transmitted?
  if (wait) {
    uint8_t s = 0u;
    while (s < ctx->nstreams) {
      usb_logging_stream_t *stream = &ctx->streams[s];
      if (!stream_close(ctx, stream)) {
        TRY(usb_testutils_poll(ctx->usbutils));
        // Stay with this logging stream until it completes.
        continue;
      }
      // Check the next logging stream.
      ++s;
    }
  }

  // Optionally finalize the testutils layer, disconnecting us from the USB.
  if (disconnect) {
    TRY(usb_testutils_fin(ctx->usbutils));
    ctx->usbutils = NULL;
  }

  return OK_STATUS();
}
