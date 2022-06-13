// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/usb_testutils_simpleserial.h"

#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/usb_testutils.h"

#define MAX_GATHER 16

static void ss_rx(void *ssctx_v, dif_usbdev_rx_packet_info_t packet_info,
                  dif_usbdev_buffer_t buffer) {
  usb_testutils_ss_ctx_t *ssctx = (usb_testutils_ss_ctx_t *)ssctx_v;
  usb_testutils_ctx_t *ctx = ssctx->ctx;

  while (packet_info.length--) {
    uint8_t data;
    size_t bytes_written;
    CHECK_DIF_OK(dif_usbdev_buffer_read(ctx->dev, ctx->buffer_pool, &buffer,
                                        &data, sizeof(data), &bytes_written));
    ssctx->got_byte(data);
  }
}

// Called periodically by the main loop to ensure characters don't
// stick around too long
static void ss_flush(void *ssctx_v) {
  usb_testutils_ss_ctx_t *ssctx = (usb_testutils_ss_ctx_t *)ssctx_v;
  usb_testutils_ctx_t *ctx = ssctx->ctx;
  if (ssctx->cur_cpos <= 0) {
    return;
  }
  if ((ssctx->cur_cpos & 0x3) != 0) {
    size_t bytes_written;
    CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &ssctx->cur_buf,
                                         ssctx->chold.data_b, /*src_len=*/4,
                                         &bytes_written));
  }
  CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ssctx->ep, &ssctx->cur_buf));
  ssctx->cur_cpos = -1;  // given it to the hardware
}

// Simple send byte will gather data for a while and send
void usb_testutils_simpleserial_send_byte(usb_testutils_ss_ctx_t *ssctx,
                                          uint8_t c) {
  usb_testutils_ctx_t *ctx = ssctx->ctx;
  if (ssctx->cur_cpos == -1) {
    CHECK_DIF_OK(
        dif_usbdev_buffer_request(ctx->dev, ctx->buffer_pool, &ssctx->cur_buf));
    ssctx->cur_cpos = 0;
  }
  ssctx->chold.data_b[ssctx->cur_cpos++ & 0x3] = c;
  if ((ssctx->cur_cpos & 0x3) == 0) {
    size_t bytes_written;
    CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &ssctx->cur_buf,
                                         ssctx->chold.data_b, /*src_len=*/4,
                                         &bytes_written));
    if (ssctx->cur_cpos >= MAX_GATHER) {
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ssctx->ep, &ssctx->cur_buf));
      ssctx->cur_cpos = -1;  // given it to the hardware
    }
  }
}

void usb_testutils_simpleserial_init(usb_testutils_ss_ctx_t *ssctx,
                                     usb_testutils_ctx_t *ctx, int ep,
                                     void (*got_byte)(uint8_t)) {
  usb_testutils_endpoint_setup(ctx, ep, kUsbdevOutStream, ssctx, NULL, ss_rx,
                               ss_flush, NULL);
  ssctx->ctx = ctx;
  ssctx->ep = ep;
  ssctx->got_byte = got_byte;
  ssctx->cur_cpos = -1;
}
