// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef __USB_SIMPLESERIAL_H__
#define __USB_SIMPLESERIAL_H__

#include "common.h"
#include "usbdev.h"

// This is only here because caller of _init needs it
typedef struct usb_ss_ctx {
  void *ctx;
  int ep;
  int cur_buf;
  int cur_cpos;
  union usb_ss_b2w {
    uint32_t data_w;
    uint8_t data_b[4];
  } chold;
  void (*got_byte)(uint8_t);
} usb_ss_ctx_t;

/**
 * Send a byte on a simpleserial endpoint
 * ssctx - instance context
 * c - byte to send
 */
void usb_simpleserial_send_byte(usb_ss_ctx_t *ssctx, uint8_t c);

/**
 * Initialize a simpleserial endpoint
 *
 * ctx - initialized usbdev context
 * ep - endpoint number for this instance
 * ssctx - unintialized simpleserial instance context
 * got_byte - callback function for when a byte is received
 */
void usb_simpleserial_init(usb_ss_ctx_t *ssctx, usbdev_ctx_t *ctx, int ep,
                           void (*got_byte)(uint8_t));

#endif
