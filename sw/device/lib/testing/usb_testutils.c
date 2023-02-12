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
  CHECK_DIF_OK(dif_usbdev_irq_get_state(ctx->dev, &istate));

  // Do this first to keep things going
  CHECK_DIF_OK(dif_usbdev_fill_available_fifo(ctx->dev, ctx->buffer_pool));

  // Process IN completions first so we get the fact that send completed
  // before processing a response
  if (istate & (1u << kDifUsbdevIrqPktSent)) {
    uint16_t sentep;
    CHECK_DIF_OK(dif_usbdev_get_tx_sent(ctx->dev, &sentep));
    TRC_C('a' + sentep);
    for (int ep = 0; ep < USBDEV_NUM_ENDPOINTS; ep++) {
      if (sentep & (1 << ep)) {
        // Free up the buffer and optionally callback
        CHECK_DIF_OK(
            dif_usbdev_clear_tx_status(ctx->dev, ctx->buffer_pool, ep));
        if (ctx->tx_done_callback[ep]) {
          ctx->tx_done_callback[ep](ctx->ep_ctx[ep]);
        }
      }
    }
  }

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

      uint8_t endpoint = packet_info.endpoint;
      if (ctx->rx_callback[endpoint]) {
        ctx->rx_callback[endpoint](ctx->ep_ctx[endpoint], packet_info, buffer);
      } else {
        TRC_S("USB: unexpected RX ");
        TRC_I(rxinfo, 24);
        CHECK_DIF_OK(
            dif_usbdev_buffer_return(ctx->dev, ctx->buffer_pool, &buffer));
      }
    }
  }
  if (istate & (1u << kDifUsbdevIrqLinkReset)) {
    TRC_S("USB: Bus reset");
    // Link reset
    for (int ep = 0; ep < USBDEV_NUM_ENDPOINTS; ep++) {
      if (ctx->reset[ep]) {
        ctx->reset[ep](ctx->ep_ctx[ep]);
      }
    }
  }
  if (istate &
      ~((1u << kDifUsbdevIrqLinkReset) | (1u << kDifUsbdevIrqPktReceived) |
        (1u << kDifUsbdevIrqPktSent))) {
    TRC_C('I');
    TRC_I(istate, 12);
    TRC_C(' ');
  }
  // Clear the interupts
  CHECK_DIF_OK(dif_usbdev_irq_acknowledge_all(ctx->dev));

  // TODO - clean this up
  // Frame ticks every 1ms, use to flush data every 16ms
  // (faster in DPI but this seems to work ok)
  // At reset frame count is 0, compare to 1 so no calls before SOF received
  uint16_t usbframe;
  CHECK_DIF_OK(dif_usbdev_status_get_frame(ctx->dev, &usbframe));
  if ((usbframe & 0xf) == 1) {
    if (ctx->flushed == 0) {
      for (int i = 0; i < USBDEV_NUM_ENDPOINTS; i++) {
        if (ctx->flush[i]) {
          ctx->flush[i](ctx->ep_ctx[i]);
        }
      }
      ctx->flushed = 1;
    }
  } else {
    ctx->flushed = 0;
  }
  // TODO Errors? What Errors?
}

void usb_testutils_endpoint_setup(
    usb_testutils_ctx_t *ctx, int ep,
    usb_testutils_out_transfer_mode_t out_mode, void *ep_ctx,
    void (*tx_done)(void *),
    void (*rx)(void *, dif_usbdev_rx_packet_info_t, dif_usbdev_buffer_t),
    void (*flush)(void *), void (*reset)(void *)) {
  ctx->ep_ctx[ep] = ep_ctx;
  ctx->tx_done_callback[ep] = tx_done;
  ctx->rx_callback[ep] = rx;
  ctx->flush[ep] = flush;
  ctx->reset[ep] = reset;

  dif_usbdev_endpoint_id_t endpoint = {
      .number = ep,
      .direction = USBDEV_ENDPOINT_DIR_IN,
  };
  CHECK_DIF_OK(
      dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));

  endpoint.direction = USBDEV_ENDPOINT_DIR_OUT;
  if (out_mode != kUsbdevOutDisabled) {
    CHECK_DIF_OK(
        dif_usbdev_endpoint_enable(ctx->dev, endpoint, kDifToggleEnabled));
    CHECK_DIF_OK(dif_usbdev_endpoint_out_enable(ctx->dev, endpoint.number,
                                                kDifToggleEnabled));
  }
  if (out_mode == kUsbdevOutMessage) {
    CHECK_DIF_OK(dif_usbdev_endpoint_set_nak_out_enable(
        ctx->dev, endpoint.number, kDifToggleEnabled));
  }
}

void usb_testutils_init(usb_testutils_ctx_t *ctx, bool pinflip,
                        bool en_diff_rcvr, bool tx_use_d_se0) {
  CHECK(ctx != NULL);
  ctx->dev = &usbdev;
  ctx->buffer_pool = &buffer_pool;

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

  // setup context
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
