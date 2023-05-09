// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/usb_testutils.h"

#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

static dif_usbdev_t usbdev;
static dif_usbdev_buffer_pool_t buffer_pool;

// Internal function to create the packet that will form the next part of a
// larger buffer transfer
static bool usb_testutils_part_prepare(usb_testutils_ctx_t *ctx,
                                       usb_testutils_transfer_t *transfer,
                                       dif_usbdev_buffer_t *next_part,
                                       bool *last) {
  CHECK(ctx && transfer && last);

  // Allocate and fill a packet buffer
  dif_result_t result =
      dif_usbdev_buffer_request(ctx->dev, ctx->buffer_pool, next_part);
  if (result != kDifOk) {
    return false;
  }

  // Determine the maximum bytes/packet
  unsigned max_packet = USBDEV_MAX_PACKET_SIZE;
  if (transfer->flags & kUsbTestutilsXfrMaxPacketSupplied) {
    max_packet = (unsigned)(transfer->flags & kUsbTestutilsXfrMaxPacketMask);
  }

  // How much are we sending this time?
  unsigned part_len = transfer->length - transfer->offset;
  if (part_len > max_packet) {
    part_len = max_packet;
  }
  size_t bytes_written = 0U;
  if (part_len) {
    CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, next_part,
                                         &transfer->buffer[transfer->offset],
                                         part_len, &bytes_written));
  }
  //  Is this the last packet?
  uint32_t next_offset = transfer->offset + bytes_written;
  *last = true;
  if (bytes_written == max_packet) {
    if (next_offset < transfer->length ||
        (transfer->flags & kUsbTestutilsXfrEmployZLP)) {
      *last = false;
    }
  } else {
    CHECK(bytes_written < max_packet);
  }

  transfer->offset = next_offset;
  return true;
}

// Internal function to perform the next part of a larger buffer transfer
static bool usb_testutils_transfer_next_part(
    usb_testutils_ctx_t *ctx, uint8_t ep, usb_testutils_transfer_t *transfer) {
  // Do we need to prepare a packet?
  if (!transfer->next_valid &&
      !usb_testutils_part_prepare(ctx, transfer, &transfer->next_part,
                                  &transfer->last)) {
    return false;
  }

  // Send the existing prepared packet
  CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ep, &transfer->next_part));
  transfer->next_valid = false;

  // If we're double-buffering, request and fill another buffer immediately;
  // we'll then be able to supply it much more promptly later...
  if ((transfer->flags & kUsbTestutilsXfrDoubleBuffered) && !transfer->last) {
    transfer->next_valid = usb_testutils_part_prepare(
        ctx, transfer, &transfer->next_part, &transfer->last);
  }

  return true;
}

status_t usb_testutils_poll(usb_testutils_ctx_t *ctx) {
  uint32_t istate;

  // Collect a set of interrupts
  TRY(dif_usbdev_irq_get_state(ctx->dev, &istate));

  if (!istate) {
    return OK_STATUS();
  }

  // Process IN completions first so we get the fact that send completed
  // before processing a response to that transmission
  // This is also important for device IN performance
  if (istate & (1u << kDifUsbdevIrqPktSent)) {
    uint16_t sentep;
    TRY(dif_usbdev_get_tx_sent(ctx->dev, &sentep));
    TRC_C('a' + sentep);
    unsigned ep = 0u;
    while (sentep && ep < USBDEV_NUM_ENDPOINTS) {
      if (sentep & (1u << ep)) {
        // Free up the buffer and optionally callback
        TRY(dif_usbdev_clear_tx_status(ctx->dev, ctx->buffer_pool,
                                       (uint8_t)ep));

        // If we have a larger transfer in progress, continue with that
        usb_testutils_transfer_t *transfer = &ctx->in[ep].transfer;
        usb_testutils_xfr_result_t res = kUsbTestutilsXfrResultOk;
        bool done = true;
        if (transfer->buffer) {
          if (transfer->next_valid || !transfer->last) {
            if (usb_testutils_transfer_next_part(ctx, (uint8_t)ep, transfer)) {
              done = false;
            } else {
              res = kUsbTestutilsXfrResultFailed;
            }
          }
          if (done) {
            // Larger buffer transfer now completed; forget the buffer
            transfer->buffer = NULL;
          }
        }
        // Notify that we've sent the single packet, or larger buffer transfer
        // is now complete
        if (done && ctx->in[ep].tx_done_callback) {
          TRY(ctx->in[ep].tx_done_callback(ctx->in[ep].ep_ctx, res));
        }
        sentep &= ~(1u << ep);
      }
      ep++;
    }
  }

  // Keep buffers available for packet reception
  TRY(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));

  if (istate & (1u << kDifUsbdevIrqPktReceived)) {
    // TODO: we run the risk of starving the IN side here if the rx_callback(s)
    // are time-consuming
    while (true) {
      bool is_empty;
      TRY(dif_usbdev_status_get_rx_fifo_empty(ctx->dev, &is_empty));
      if (is_empty) {
        break;
      }

      dif_usbdev_rx_packet_info_t packet_info;
      dif_usbdev_buffer_t buffer;
      TRY(dif_usbdev_recv(ctx->dev, &packet_info, &buffer));

      unsigned ep = packet_info.endpoint;
      if (ctx->out[ep].rx_callback) {
        TRY(ctx->out[ep].rx_callback(ctx->out[ep].ep_ctx, packet_info, buffer));
      } else {
        // Note: this could happen following endpoint removal
        TRC_S("USB: unexpected RX ");
        TRC_I(ep, 8);
        TRY(dif_usbdev_buffer_return(ctx->dev, ctx->buffer_pool, &buffer));
      }
    }
  }
  if (istate & (1u << kDifUsbdevIrqLinkReset)) {
    TRC_S("USB: Bus reset");
    // Link reset
    for (int ep = 0; ep < USBDEV_NUM_ENDPOINTS; ep++) {
      // Notify the IN endpoint first because transmission is more significantly
      // impacted, and then the OUT endpoint before advancing to the next
      // endpoint number in case the order is important to the client(s)
      if (ctx->in[ep].reset) {
        TRY(ctx->in[ep].reset(ctx->in[ep].ep_ctx));
      }
      if (ctx->out[ep].reset) {
        TRY(ctx->out[ep].reset(ctx->out[ep].ep_ctx));
      }
    }
  }

  // Clear the interrupts that we've received and handled
  TRY(dif_usbdev_irq_acknowledge_state(ctx->dev, istate));

  // Record bus frame
  if ((istate & (1u << kDifUsbdevIrqFrame))) {
    // The first bus frame is 1
    TRY(dif_usbdev_status_get_frame(ctx->dev, &ctx->frame));
    ctx->got_frame = true;
  }

  // Note: LinkInErr will be raised in response to a packet being NAKed by the
  // host which is not expected behavior on a physical USB but this is something
  // that the DPI model does to exercise packet resending when running
  // usbdev_stream_test
  //
  // We can expect AVFIFO empty and RXFIFO full interrupts when using a real
  // host and also 'LinkOut' errors because these can be triggered by a lack of
  // space in the RXFIFO

  if (istate &
      ~((1u << kDifUsbdevIrqLinkReset) | (1u << kDifUsbdevIrqPktReceived) |
        (1u << kDifUsbdevIrqPktSent) | (1u << kDifUsbdevIrqFrame) |
        (1u << kDifUsbdevIrqAvEmpty) | (1u << kDifUsbdevIrqRxFull) |
        (1u << kDifUsbdevIrqLinkOutErr) | (1u << kDifUsbdevIrqLinkInErr))) {
    // Report anything that really should not be happening during testing,
    //   at least for now
    //
    // TODO - introduce deliberate generation of each of these errors, and
    //        modify usb_testutils_ to return the information without faulting
    //        it?
    if (istate &
        ((1u << kDifUsbdevIrqRxFull) | (1u << kDifUsbdevIrqAvOverflow) |
         (1u << kDifUsbdevIrqLinkInErr) | (1u << kDifUsbdevIrqRxCrcErr) |
         (1u << kDifUsbdevIrqRxPidErr) | (1u << kDifUsbdevIrqRxBitstuffErr) |
         (1u << kDifUsbdevIrqLinkOutErr))) {
      LOG_INFO("USB: Unexpected interrupts: 0x%08x", istate);
    } else {
      // Other events are optionally reported
      TRC_C('I');
      TRC_I(istate, 12);
      TRC_C(' ');
    }
  }

  // TODO - clean this up
  // Frame ticks every 1ms, use to flush data every 16ms
  // (faster in DPI but this seems to work ok)
  //
  // Ensure that we do not flush until we have received a frame
  if (ctx->got_frame && (ctx->frame & 0xf) == 1) {
    if (ctx->flushed == 0) {
      for (unsigned ep = 0; ep < USBDEV_NUM_ENDPOINTS; ep++) {
        if (ctx->in[ep].flush) {
          TRY(ctx->in[ep].flush(ctx->in[ep].ep_ctx));
        }
      }
      ctx->flushed = 1;
    }
  } else {
    ctx->flushed = 0;
  }
  // TODO Errors? What Errors?
  return OK_STATUS();
}

status_t usb_testutils_transfer_send(usb_testutils_ctx_t *ctx, uint8_t ep,
                                     const uint8_t *data, uint32_t length,
                                     usb_testutils_xfr_flags_t flags) {
  CHECK(ep < USBDEV_NUM_ENDPOINTS);

  usb_testutils_transfer_t *transfer = &ctx->in[ep].transfer;
  if (transfer->buffer) {
    // If there is an in-progress transfer, then we cannot accept another
    return OK_STATUS(false);
  }

  // Describe this transfer
  transfer->buffer = data;
  transfer->offset = 0U;
  transfer->length = length;
  transfer->flags = flags;
  transfer->next_valid = false;

  if (!usb_testutils_transfer_next_part(ctx, ep, transfer)) {
    // Forget about the attempted transfer
    transfer->buffer = NULL;
    return OK_STATUS(false);
  }

  // Buffer transfer is underway...
  return OK_STATUS(true);
}

status_t usb_testutils_in_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep, void *ep_ctx,
    usb_testutils_tx_done_handler_t tx_done,
    usb_testutils_tx_flush_handler_t flush,
    usb_testutils_reset_handler_t reset) {
  ctx->in[ep].ep_ctx = ep_ctx;
  ctx->in[ep].tx_done_callback = tx_done;
  ctx->in[ep].flush = flush;
  ctx->in[ep].reset = reset;

  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_IN,
  };

  TRY(dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));

  // Enable IN traffic from device to host
  TRY(dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));
  return OK_STATUS();
}

status_t usb_testutils_out_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    usb_testutils_rx_handler_t rx, usb_testutils_reset_handler_t reset) {
  ctx->out[ep].ep_ctx = ep_ctx;
  ctx->out[ep].rx_callback = rx;
  ctx->out[ep].reset = reset;

  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_OUT,
  };

  TRY(dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));

  // Enable/disable the endpoint and reception of OUT packets?
  dif_toggle_t enabled = kDifToggleEnabled;
  if (out_mode == kUsbdevOutDisabled) {
    enabled = kDifToggleDisabled;
  }
  // Enable/disable generation of NAK responses once OUT packet has been
  // received?
  dif_toggle_t nak = kDifToggleDisabled;
  if (out_mode == kUsbdevOutMessage) {
    nak = kDifToggleEnabled;
  }

  TRY(dif_usbdev_endpoint_enable(ctx->dev, endpoint, enabled));
  TRY(dif_usbdev_endpoint_out_enable(ctx->dev, ep, enabled));
  TRY(dif_usbdev_endpoint_set_nak_out_enable(ctx->dev, ep, nak));
  return OK_STATUS();
}

status_t usb_testutils_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    usb_testutils_tx_done_handler_t tx_done, usb_testutils_rx_handler_t rx,
    usb_testutils_tx_flush_handler_t flush,
    usb_testutils_reset_handler_t reset) {
  TRY(usb_testutils_in_endpoint_setup(ctx, ep, ep_ctx, tx_done, flush, reset));

  // Note: register the link reset handler only on the IN endpoint so that it
  // does not get invoked twice
  return usb_testutils_out_endpoint_setup(ctx, ep, out_mode, ep_ctx, rx, NULL);
}

status_t usb_testutils_in_endpoint_remove(usb_testutils_ctx_t *ctx,
                                          uint8_t ep) {
  // Disable IN traffic
  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_IN,
  };
  TRY(dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleDisabled));

  // Remove callback handlers
  ctx->in[ep].tx_done_callback = NULL;
  ctx->in[ep].flush = NULL;
  ctx->in[ep].reset = NULL;

  return OK_STATUS();
}

status_t usb_testutils_out_endpoint_remove(usb_testutils_ctx_t *ctx,
                                           uint8_t ep) {
  // Disable OUT traffic
  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_OUT,
  };
  TRY(dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleDisabled));

  // Return the rest of the OUT endpoint configuration to its default state
  TRY(dif_usbdev_endpoint_set_nak_out_enable(ctx->dev, endpoint.number,
                                             kDifToggleDisabled));
  TRY(dif_usbdev_endpoint_out_enable(ctx->dev, endpoint.number,
                                     kDifToggleDisabled));

  // Remove callback handlers
  ctx->out[ep].rx_callback = NULL;
  ctx->out[ep].reset = NULL;

  return OK_STATUS();
}

status_t usb_testutils_endpoint_remove(usb_testutils_ctx_t *ctx, uint8_t ep) {
  TRY(usb_testutils_in_endpoint_remove(ctx, ep));
  return usb_testutils_out_endpoint_remove(ctx, ep);
}

status_t usb_testutils_init(usb_testutils_ctx_t *ctx, bool pinflip,
                            bool en_diff_rcvr, bool tx_use_d_se0) {
  TRY_CHECK(ctx != NULL);
  ctx->dev = &usbdev;
  ctx->buffer_pool = &buffer_pool;

  // Ensure that we do not invoke the endpoint 'flush' functions before
  // detection of the first bus frame
  ctx->got_frame = false;
  ctx->frame = 0u;

  TRY(dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), ctx->dev));

  dif_usbdev_config_t config = {
      .have_differential_receiver = dif_bool_to_toggle(en_diff_rcvr),
      .use_tx_d_se0 = dif_bool_to_toggle(tx_use_d_se0),
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = dif_bool_to_toggle(pinflip),
      .clock_sync_signals = kDifToggleEnabled,
  };
  TRY(dif_usbdev_configure(ctx->dev, ctx->buffer_pool, config));

  // Set up context
  static_assert(USBDEV_NUM_ENDPOINTS <= UINT8_MAX,
                "USBDEV_NUM_ENDPOINTS must fit into uint8_t");
  for (uint8_t i = 0; i < USBDEV_NUM_ENDPOINTS; i++) {
    TRY(usb_testutils_endpoint_setup(ctx, i, kUsbdevOutDisabled, NULL, NULL,
                                     NULL, NULL, NULL));
  }

  // All about polling...
  TRY(dif_usbdev_irq_disable_all(ctx->dev, NULL));

  // Provide buffers for any packet reception
  TRY(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));

  // Preemptively enable SETUP reception on endpoint zero for the
  // Default Control Pipe; all other settings for that endpoint will be applied
  // once the callback handlers are registered by a call to _endpoint_setup()
  TRY(dif_usbdev_endpoint_setup_enable(ctx->dev, 0, kDifToggleEnabled));

  return OK_STATUS();
}

status_t usb_testutils_fin(usb_testutils_ctx_t *ctx) {
  // Remove the endpoints in reverse order so that Endpoint Zero goes down last
  static_assert(USBDEV_NUM_ENDPOINTS <= UINT8_MAX,
                "USBDEV_NUM_ENDPOINTS must fit into uint8_t");
  static_assert(USBDEV_NUM_ENDPOINTS > 0,
                "USBDEV_NUM_ENDPOINTS - 1 must not overflow");
  for (uint8_t ep = USBDEV_NUM_ENDPOINTS - 1; ep >= 0; ep--) {
    TRY(usb_testutils_endpoint_remove(ctx, ep));
  }

  // Disconnect from the bus
  TRY(dif_usbdev_interface_enable(ctx->dev, kDifToggleDisabled));
  return OK_STATUS();
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern int usb_testutils_halted(usb_testutils_ctx_t *ctx,
                                dif_usbdev_endpoint_id_t endpoint);
