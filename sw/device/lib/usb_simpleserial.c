// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/usb_simpleserial.h"

#include "sw/device/lib/usbdev.h"

#define MAX_GATHER 16

static void ss_rx(void *ssctx_v, usbbufid_t buf, int size, int setup) {
  usb_ss_ctx_t *ssctx = (usb_ss_ctx_t *)ssctx_v;
  void *ctx = ssctx->ctx;
  volatile uint8_t *bp = (volatile uint8_t *)usbdev_buf_idtoaddr(ctx, buf);

  if (size > BUF_LENGTH) {
    size = BUF_LENGTH;
  }

  while (size--) {
    ssctx->got_byte(*bp++);
  }
}

// Called periodically by the main loop to ensure characters don't
// stick around too long
static void ss_flush(void *ssctx_v) {
  usb_ss_ctx_t *ssctx = (usb_ss_ctx_t *)ssctx_v;
  void *ctx = ssctx->ctx;
  volatile uint32_t *bp_w;
  if ((ssctx->cur_buf == -1) || (ssctx->cur_cpos <= 0)) {
    return;
  }
  if ((ssctx->cur_cpos & 0x3) != 0) {
    // unwritten data to copy over
    bp_w = usbdev_buf_idtoaddr(ctx, ssctx->cur_buf);
    // no -1 here because cpos is in the word we are writing
    bp_w[(ssctx->cur_cpos / 4)] = ssctx->chold.data_w;
  }
  usbdev_sendbuf_byid(ctx, ssctx->cur_buf, ssctx->cur_cpos, ssctx->ep);
  ssctx->cur_buf = -1;  // given it to the hardware
}

// Simple send byte will gather data for a while and send
void usb_simpleserial_send_byte(usb_ss_ctx_t *ssctx, uint8_t c) {
  volatile uint32_t *bp_w;
  if (ssctx->cur_buf == -1) {
    ssctx->cur_buf = usbdev_buf_allocate_byid(ssctx->ctx);
    ssctx->cur_cpos = 0;
  }
  // Abort if completely out of buffers and allocation returned -1
  if (ssctx->cur_buf < 0) {
    return;
  }
  ssctx->chold.data_b[ssctx->cur_cpos++ & 0x3] = c;
  if ((ssctx->cur_cpos & 0x3) == 0) {
    // just wrote last byte in word
    bp_w = usbdev_buf_idtoaddr(ssctx->ctx, ssctx->cur_buf);
    // -1 here because cpos already incremented to next word
    bp_w[(ssctx->cur_cpos / 4) - 1] = ssctx->chold.data_w;
    if (ssctx->cur_cpos >= MAX_GATHER) {
      usbdev_sendbuf_byid(ssctx->ctx, ssctx->cur_buf, ssctx->cur_cpos,
                          ssctx->ep);
      ssctx->cur_buf = -1;  // given it to the hardware
    }
  }
}

void usb_simpleserial_init(usb_ss_ctx_t *ssctx, usbdev_ctx_t *ctx, int ep,
                           void (*got_byte)(uint8_t)) {
  usbdev_endpoint_setup(ctx, ep, 1, ssctx, NULL, ss_rx, ss_flush, NULL);
  ssctx->ctx = ctx;
  ssctx->ep = ep;
  ssctx->got_byte = got_byte;
  ssctx->cur_buf = -1;
}
