// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_USB_SIMPLESERIAL_H_
#define OPENTITAN_SW_DEVICE_LIB_USB_SIMPLESERIAL_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/usbdev.h"

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
 *
 * @param ssctx instance context
 * @param c byte to send
 */
void usb_simpleserial_send_byte(usb_ss_ctx_t *ssctx, uint8_t c);

/**
 * Initialize a simpleserial endpoint
 *
 * @param ssctx unintialized simpleserial instance context
 * @param ctx initialized usbdev context
 * @param ep endpoint number for this instance
 * @param got_byte callback function for when a byte is received
 */
void usb_simpleserial_init(usb_ss_ctx_t *ssctx, usbdev_ctx_t *ctx, int ep,
                           void (*got_byte)(uint8_t));

#endif  // OPENTITAN_SW_DEVICE_LIB_USB_SIMPLESERIAL_H_
