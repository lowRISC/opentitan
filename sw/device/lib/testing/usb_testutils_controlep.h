// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_CONTROLEP_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_CONTROLEP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/usb_testutils.h"

typedef enum usb_testutils_ctstate {
  kUsbTestutilsCtIdle,
  kUsbTestutilsCtWaitIn,      // Queued IN data stage, waiting ack
  kUsbTestutilsCtStatOut,     // Waiting for OUT status stage
  kUsbTestutilsCtAddrStatIn,  // Queued status stage, waiting ack.
                              // After which, set dev_addr
  kUsbTestutilsCtStatIn,      // Queued status stage, waiting ack
  kUsbTestutilsCtError        // Something bad
} usb_testutils_ctstate_t;

typedef enum usb_testutils_device_state {
  kUsbTestutilsDeviceAttached,
  kUsbTestutilsDevicePowered,
  kUsbTestutilsDeviceDefault,
  kUsbTestutilsDeviceAddressed,
  kUsbTestutilsDeviceConfigured,
  kUsbTestutilsDeviceSuspended,
} usb_testutils_device_state_t;

typedef struct usb_testutils_controlep_ctx {
  usb_testutils_ctx_t *ctx;
  int ep;
  usb_testutils_ctstate_t ctrlstate;
  usb_testutils_device_state_t device_state;
  uint32_t new_dev;
  uint8_t usb_config;
  /**
   * USB configuration descriptor
   */
  const uint8_t *cfg_dscr;
  size_t cfg_dscr_len;
  /**
   * Optional test descriptor, or NULL
   */
  const uint8_t *test_dscr;
  size_t test_dscr_len;
} usb_testutils_controlep_ctx_t;

/**
 * Initialize control endpoint
 *
 * @param ctctx uninitialized context for this instance
 * @param ctx initialized context for usbdev driver
 * @param ep endpoint (if this is other than 0 make sure you know why)
 * @param cfg_dscr configuration descriptor for the device
 * @param cfg_dscr_len length of cfg_dscr
 * @param test_dscr optional test descriptor, or NULL
 * @param test_dscr_len length of test_dscr
 * @return The result of the operation
 */
OT_WARN_UNUSED_RESULT
status_t usb_testutils_controlep_init(usb_testutils_controlep_ctx_t *ctctx,
                                      usb_testutils_ctx_t *ctx, int ep,
                                      const uint8_t *cfg_dscr,
                                      size_t cfg_dscr_len,
                                      const uint8_t *test_dscr,
                                      size_t test_dscr_len);

/***********************************************************************/
/* Below this point are macros used to construct the USB configuration */
/* descriptor. Use them to initialize a uint8_t array for cfg_dscr     */

#define USB_CFG_DSCR_LEN 9
#define USB_CFG_DSCR_HEAD(total_len, nint)                                   \
  /* This is the actual configuration descriptor                 */          \
  USB_CFG_DSCR_LEN,     /* bLength                                   */      \
      2,                /* bDescriptorType                           */      \
      (total_len)&0xff, /* wTotalLength[0]                           */      \
      (total_len) >> 8, /* wTotalLength[1]                           */      \
      (nint),           /* bNumInterfaces                            */      \
      1,                /* bConfigurationValue                       */      \
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
#define USB_EP_DSCR(in, ep, attr, maxsize, interval)                          \
  /* endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13   */       \
  USB_EP_DSCR_LEN,                 /* bLength                              */ \
      5,                           /* bDescriptorType                      */ \
      (ep) | (((in) << 7) & 0x80), /* bEndpointAddress, top bit set for IN */ \
      attr,                        /* bmAttributes                         */ \
      (maxsize)&0xff,              /* wMaxPacketSize[0]                    */ \
      (maxsize) >> 8,              /* wMaxPacketSize[1]                    */ \
      (interval)                   /* bInterval                            */

// KEEP BLANK LINE ABOVE, it is in the macro!
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

/***********************************************************************/
/* Below this point are macros used to construct the test descriptor   */
/* Use them to initialize a uint8_t array for test_dscr                */
#define USB_TESTUTILS_TEST_DSCR_LEN 0x10u
#define USB_TESTUTILS_TEST_DSCR(num, arg0, arg1, arg2, arg3)            \
  0x7e, 0x57, 0xc0, 0xf1u,                /* Header signature        */ \
      (USB_TESTUTILS_TEST_DSCR_LEN)&0xff, /* Descriptor length[0]    */ \
      (USB_TESTUTILS_TEST_DSCR_LEN) >> 8, /* Descriptor length[1]    */ \
      (num)&0xff,                         /* Test number[0]          */ \
      (num) >> 8,                         /* Test number[1]          */ \
      (arg0), (arg1), (arg2), (arg3),     /* Test-specific arugments */ \
      0x1fu, 0x0cu, 0x75, 0xe7u           /* Tail signature */

// KEEP BLANK LINE ABOVE, it is in the macro!

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_CONTROLEP_H_
