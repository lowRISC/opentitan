// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_USB_CONTROLEP_H_
#define OPENTITAN_SW_DEVICE_LIB_USB_CONTROLEP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/usbdev.h"

typedef enum ctstate {
  kCtIdle,
  kCtWaitIn,      // Queued IN data stage, waiting ack
  kCtStatOut,     // Waiting for OUT status stage
  kCtAddrStatIn,  // Queued status stage, waiting ack afterwhich set dev_addr
  kCtStatIn,      // Queued status stage, waiting ack
  kCtError        // Something bad
} ctstate_t;

typedef struct usb_controlep_ctx {
  usbdev_ctx_t *ctx;
  int ep;
  ctstate_t ctrlstate;
  uint32_t new_dev;
  uint8_t usb_config;
  const uint8_t *cfg_dscr;
  size_t cfg_dscr_len;
} usb_controlep_ctx_t;

/**
 * Initialize control endpoint
 *
 * @param ctctx uninitialized context for this instance
 * @param ctx initialized context for usbdev driver
 * @param ep endpoint (if this is other than 0 make sure you know why)
 * @param cfg_dscr configuration descriptor for the device
 * @param cfg_dscr_len length of cfg_dscr
 */
void usb_controlep_init(usb_controlep_ctx_t *ctctx, usbdev_ctx_t *ctx, int ep,
                        const uint8_t *cfg_dscr, size_t cfg_dscr_len);

/********************************************************************/
/* Below this point are macros used to construct the USB descriptor */
/* Use them to initialize a uint8_t array for cfg_dscr              */

#define USB_CFG_DSCR_LEN 9
#define USB_CFG_DSCR_HEAD(total_len, nint)                                   \
  /* This is the actual configuration descriptor                 */          \
  USB_CFG_DSCR_LEN,     /* bLength                                   */      \
      2,                /* bDescriptorType                           */      \
      (total_len)&0xff, /* wTotalLength[0]                           */      \
      (total_len) >> 8, /* wTotalLength[1]                           */      \
      (nint),           /* bNumInterfaces                            */      \
      1,                /* bConfigurationValu                        */      \
      0,                /* iConfiguration                            */      \
      0xC0,             /* bmAttributes: must-be-one, self-powered   */      \
      50 /* bMaxPower                                 */ /* MUST be followed \
                                                            by (nint)        \
                                                            Interface +      \
                                                            Endpoint         \
                                                            Descriptors */

// KEEP BLANK LINE ABOVE, it is in the macro!

#define USB_INTERFACE_DSCR_LEN 9
#define VEND_INTERFACE_DSCR(inum, nep, subclass, protocol)               \
  /* interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12 */   \
  USB_INTERFACE_DSCR_LEN, /* bLength                             */      \
      4,                  /* bDescriptorType                     */      \
      (inum),             /* bInterfaceNumber                    */      \
      0,                  /* bAlternateSetting                   */      \
      (nep),              /* bNumEndpoints                       */      \
      0xff,               /* bInterfaceClass (Vendor Specific)   */      \
      (subclass),         /* bInterfaceSubClass                  */      \
      (protocol),         /* bInterfaceProtocol                  */      \
      0 /* iInterface                          */ /* MUST be followed by \
                                                     (nep) Endpoint      \
                                                     Descriptors */

// KEEP BLANK LINE ABOVE, it is in the macro!

#define USB_EP_DSCR_LEN 7
#define USB_BULK_EP_DSCR(in, ep, maxsize, interval)                           \
  /* endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13   */       \
  USB_EP_DSCR_LEN,                 /* bLength                              */ \
      5,                           /* bDescriptorType                      */ \
      (ep) | (((in) << 7) & 0x80), /* bEndpointAddress, top bit set for IN */ \
      0x02,                        /* bmAttributes (0x02=bulk, data)       */ \
      (maxsize)&0xff,              /* wMaxPacketSize[0]                    */ \
      (maxsize) >> 8,              /* wMaxPacketSize[1]                    */ \
      (interval)                   /* bInterval                            */

// KEEP BLANK LINE ABOVE, it is in the macro!

#endif  // OPENTITAN_SW_DEVICE_LIB_USB_CONTROLEP_H_
