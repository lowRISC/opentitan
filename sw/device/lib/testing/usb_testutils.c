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

void usb_testutils_poll(usb_testutils_ctx_t *ctx) {
  uint32_t istate;

  // Collect a set of interrupts
  CHECK_DIF_OK(dif_usbdev_irq_get_state(ctx->dev, &istate));

  if (!istate) {
    // Nothing new to do right now, but keep buffers available for reception
    CHECK_DIF_OK(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));
    return;
  }

  // Record bus frame
  if ((istate & (1u << kDifUsbdevIrqFrame))) {
    // The first bus frame is 1
    CHECK_DIF_OK(dif_usbdev_status_get_frame(ctx->dev, &ctx->frame));
    ctx->got_frame = true;
  }

  // Process IN completions first so we get the fact that send completed
  // before processing a response to that transmission
  // This is also important for device IN performance
  if (istate & (1u << kDifUsbdevIrqPktSent)) {
    uint16_t sentep;
    CHECK_DIF_OK(dif_usbdev_get_tx_sent(ctx->dev, &sentep));
    TRC_C('a' + sentep);
    for (unsigned ep = 0; ep < USBDEV_NUM_ENDPOINTS; ep++) {
      if (sentep & (1 << ep)) {
        // Free up the buffer and optionally callback
        CHECK_DIF_OK(
            dif_usbdev_clear_tx_status(ctx->dev, ctx->buffer_pool, ep));

        if (ctx->in[ep].tx_done_callback) {
          ctx->in[ep].tx_done_callback(ctx->in[ep].ep_ctx);
        }
      }
    }

    // Clear the interrupt sooner so that we can respond more promptly to
    // subsequent transmitted packets
    CHECK_DIF_OK(dif_usbdev_irq_acknowledge(ctx->dev, kDifUsbdevIrqPktSent));
    istate &= ~(1u << kDifUsbdevIrqPktSent);
  }

  // Keep buffers available for packet reception
  CHECK_DIF_OK(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));

  if (istate & (1u << kDifUsbdevIrqPktReceived)) {
    while (true) {
      bool is_empty;
      CHECK_DIF_OK(dif_usbdev_status_get_rx_fifo_empty(ctx->dev, &is_empty));
      if (is_empty) {
        break;
      }

      dif_usbdev_rx_packet_info_t packet_info;
      dif_usbdev_buffer_t buffer;
      CHECK_DIF_OK(dif_usbdev_recv(ctx->dev, &packet_info, &buffer));

      unsigned ep = packet_info.endpoint;
      if (ctx->out[ep].rx_callback) {
        ctx->out[ep].rx_callback(ctx->out[ep].ep_ctx, packet_info, buffer);
      } else {
        TRC_S("USB: unexpected RX ");
        TRC_I(endpoint, 8);
        CHECK_DIF_OK(
            dif_usbdev_buffer_return(ctx->dev, ctx->buffer_pool, &buffer));
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
        ctx->in[ep].reset(ctx->in[ep].ep_ctx);
      }
      if (ctx->out[ep].reset) {
        ctx->out[ep].reset(ctx->out[ep].ep_ctx);
      }
    }
  }

  // Clear the interrupts that we've received and handled
  CHECK_DIF_OK(dif_usbdev_irq_acknowledge_state(ctx->dev, istate));

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
          ctx->in[ep].flush(ctx->in[ep].ep_ctx);
        }
      }
      ctx->flushed = 1;
    }
  } else {
    ctx->flushed = 0;
  }
  // TODO Errors? What Errors?
}

void usb_testutils_in_endpoint_setup(usb_testutils_ctx_t *ctx, uint8_t ep,
                                     void *ep_ctx, void (*tx_done)(void *),
                                     void (*flush)(void *),
                                     void (*reset)(void *)) {
  ctx->in[ep].ep_ctx = ep_ctx;
  ctx->in[ep].tx_done_callback = tx_done;
  ctx->in[ep].flush = flush;
  ctx->in[ep].reset = reset;

  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_IN,
  };

  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));

  // Enable IN traffic from device to host
  CHECK_DIF_OK(
      dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));
}

void usb_testutils_out_endpoint_setup(
    usb_testutils_ctx_t *ctx, uint8_t ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    void (*rx)(void *, dif_usbdev_rx_packet_info_t, dif_usbdev_buffer_t),
    void (*reset)(void *)) {
  ctx->out[ep].ep_ctx = ep_ctx;
  ctx->out[ep].rx_callback = rx;
  ctx->out[ep].reset = reset;

  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_OUT,
  };

  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));

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

  CHECK_DIF_OK(dif_usbdev_endpoint_enable(ctx->dev, endpoint, enabled));
  CHECK_DIF_OK(dif_usbdev_endpoint_out_enable(ctx->dev, ep, enabled));
  CHECK_DIF_OK(dif_usbdev_endpoint_set_nak_out_enable(ctx->dev, ep, nak));
}

void usb_testutils_endpoint_setup(
    usb_testutils_ctx_t *ctx, int ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    void (*tx_done)(void *),
    void (*rx)(void *, dif_usbdev_rx_packet_info_t, dif_usbdev_buffer_t),
    void (*flush)(void *), void (*reset)(void *)) {
  usb_testutils_in_endpoint_setup(ctx, ep, ep_ctx, tx_done, flush, reset);

  // Note: register the link reset handler only on the IN endpoint so that it
  // does not get invoked twice
  usb_testutils_out_endpoint_setup(ctx, ep, out_mode, ep_ctx, rx, NULL);
}

void usb_testutils_init(usb_testutils_ctx_t *ctx, bool pinflip,
                        bool en_diff_rcvr, bool tx_use_d_se0) {
  CHECK(ctx != NULL);
  ctx->dev = &usbdev;
  ctx->buffer_pool = &buffer_pool;

  // Ensure that we do not invoke the endpoint 'flush' functions before
  // detection of the first bus frame
  ctx->got_frame = false;
  ctx->frame = 0u;

  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), ctx->dev));

  dif_usbdev_config_t config = {
      .have_differential_receiver = dif_bool_to_toggle(en_diff_rcvr),
      .use_tx_d_se0 = dif_bool_to_toggle(tx_use_d_se0),
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = dif_bool_to_toggle(pinflip),
      .clock_sync_signals = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_usbdev_configure(ctx->dev, ctx->buffer_pool, config));

  // Set up context
  for (int i = 0; i < USBDEV_NUM_ENDPOINTS; i++) {
    usb_testutils_endpoint_setup(ctx, i, kUsbdevOutDisabled, NULL, NULL, NULL,
                                 NULL, NULL);
  }

  // All about polling...
  CHECK_DIF_OK(dif_usbdev_irq_disable_all(ctx->dev, NULL));

  // Provide buffers for any reception
  CHECK_DIF_OK(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));

  dif_usbdev_endpoint_id_t endpoint = {
      .number = 0,
      .direction = 1,
  };
  CHECK_DIF_OK(
      dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));

  endpoint.direction = 0;
  CHECK_DIF_OK(
      dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleDisabled));
  CHECK_DIF_OK(dif_usbdev_endpoint_setup_enable(ctx->dev, endpoint.number,
                                                kDifToggleEnabled));
  CHECK_DIF_OK(dif_usbdev_endpoint_out_enable(ctx->dev, endpoint.number,
                                              kDifToggleEnabled));
}

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern int usb_testutils_halted(usb_testutils_ctx_t *ctx,
                                dif_usbdev_endpoint_id_t endpoint);
