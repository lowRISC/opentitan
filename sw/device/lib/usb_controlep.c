// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/usb_controlep.h"

#include "sw/device/lib/usb_consts.h"
#include "sw/device/lib/usbdev.h"

// Device descriptor
static uint8_t dev_dscr[] = {
    18,    // bLength
    1,     // bDescriptorType
    0x00,  // bcdUSB[0]
    0x02,  // bcdUSB[1]
    0x00,  // bDeviceClass (defined at interface level)
    0x00,  // bDeviceSubClass
    0x00,  // bDeviceProtocol
    64,    // bMaxPacketSize0

    0xd1,  // idVendor[0] 0x18d1 Google Inc.
    0x18,  // idVendor[1]
    0x3a,  // idProduct[0] lowRISC generic FS USB
    0x50,  // idProduct[1] (allocated by Google)

    0,    // bcdDevice[0]
    0x1,  // bcdDevice[1]
    0,    // iManufacturer
    0,    // iProduct
    0,    // iSerialNumber
    1     // bNumConfigurations
};

static ctstate_t setup_req(usb_controlep_ctx_t *ctctx, void *ctx,
                           usbbufid_t buf, int bmRequestType, int bRequest,
                           int wValue, int wIndex, int wLength) {
  size_t len;
  uint32_t stat;
  int zero, type;
  switch (bRequest) {
    case kUsbSetupReqGetDescriptor:
      if ((wValue & 0xff00) == 0x100) {
        // Device descriptor
        len = sizeof(dev_dscr);
        if (wLength < len) {
          len = wLength;
        }
        usbdev_buf_copyto_byid(ctx, buf, dev_dscr, len);
        usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
        return kCtWaitIn;
      } else if ((wValue & 0xff00) == 0x200) {
        // Configuration descriptor
        len = ctctx->cfg_dscr_len;
        if (wLength < len) {
          len = wLength;
        }
        usbdev_buf_copyto_byid(ctx, buf, ctctx->cfg_dscr, len);
        usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
        return kCtWaitIn;
      }
      return kCtError;  // unknown

    case kUsbSetupReqSetAddress:
      ctctx->new_dev = wValue & 0x7f;
      // send zero length packet for status phase
      usbdev_sendbuf_byid(ctx, buf, 0, ctctx->ep);
      return kCtAddrStatIn;

    case kUsbSetupReqSetConfiguration:
      // only ever expect this to be 1 since there is one config descriptor
      ctctx->usb_config = wValue;
      // send zero length packet for status phase
      usbdev_sendbuf_byid(ctx, buf, 0, ctctx->ep);
      return kCtStatIn;

    case kUsbSetupReqGetConfiguration:
      len = sizeof(ctctx->usb_config);
      if (wLength < len) {
        len = wLength;
      }
      // return the value that was set
      usbdev_buf_copyto_byid(ctx, buf, &ctctx->usb_config, len);
      usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
      return kCtWaitIn;

    case kUsbSetupReqSetFeature:
      if (wValue == kUsbFeatureEndpointHalt) {
        usbdev_halt(ctx, wIndex, 1);
      } else if (wValue == kUsbFeatureDeviceRemoteWakeup) {
        usbdev_rem_wake_en(ctx, 1);
      }
      // send zero length packet for status phase
      usbdev_sendbuf_byid(ctx, buf, 0, ctctx->ep);
      return kCtStatIn;

    case kUsbSetupReqClearFeature:
      if (wValue == kUsbFeatureEndpointHalt) {
        usbdev_halt(ctx, wIndex, 0);
      } else if (wValue == kUsbFeatureDeviceRemoteWakeup) {
        usbdev_rem_wake_en(ctx, 0);
      }
      // send zero length packet for status phase
      usbdev_sendbuf_byid(ctx, buf, 0, ctctx->ep);
      return kCtStatIn;

    case kUsbSetupReqGetStatus:
      len = 2;
      type = bmRequestType & kUsbReqTypeRecipientMask;
      if (type == kUsbReqTypeDevice) {
        stat = (usbdev_can_rem_wake(ctx) ? kUsbStatusRemWake : 0) |
               kUsbStatusSelfPowered;
      } else if (type == kUsbReqTypeEndpoint) {
        stat = usbdev_halted(ctx, wIndex) ? kUsbStatusHalted : 0;
      } else {
        stat = 0;
      }
      if (wLength < len) {
        len = wLength;
      }
      // return the value that was set
      usbdev_buf_copyto_byid(ctx, buf, &stat, len);
      usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
      return kCtWaitIn;

    case kUsbSetupReqSetInterface:
      // Don't support alternate interfaces, so just ignore
      // send zero length packet for status phase
      usbdev_sendbuf_byid(ctx, buf, 0, ctctx->ep);
      return kCtStatIn;

    case kUsbSetupReqGetInterface:
      zero = 0;
      len = 1;
      if (wLength < len) {
        len = wLength;
      }
      // Don't support interface, so return zero
      usbdev_buf_copyto_byid(ctx, buf, &zero, len);
      usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
      return kCtWaitIn;

    case kUsbSetupReqSynchFrame:
      zero = 0;
      len = 2;
      if (wLength < len) {
        len = wLength;
      }
      // Don't support synch_frame so return zero
      usbdev_buf_copyto_byid(ctx, buf, &zero, len);
      usbdev_sendbuf_byid(ctx, buf, len, ctctx->ep);
      return kCtWaitIn;

    default:
      return kCtError;
  }
  return kCtError;
}

static void ctrl_tx_done(void *ctctx_v) {
  usb_controlep_ctx_t *ctctx = (usb_controlep_ctx_t *)ctctx_v;
  void *ctx = ctctx->ctx;
  TRC_C('A' + ctctx->ctrlstate);
  switch (ctctx->ctrlstate) {
    case kCtAddrStatIn:
      // Now the status was sent on device 0 can switch to new device ID
      usbdev_set_deviceid(ctx, ctctx->new_dev);
      TRC_I(ctctx->new_dev, 8);
      ctctx->ctrlstate = kCtIdle;
      return;
    case kCtStatIn:
      ctctx->ctrlstate = kCtIdle;
      return;
    case kCtWaitIn:
      ctctx->ctrlstate = kCtStatOut;
      return;
    default:
      break;
  }
  TRC_S("USB: unexpected IN ");
  TRC_I((ctctx->ctrlstate << 24), 32);
}

static void ctrl_rx(void *ctctx_v, usbbufid_t buf, int size, int setup) {
  usb_controlep_ctx_t *ctctx = (usb_controlep_ctx_t *)ctctx_v;
  void *ctx = ctctx->ctx;
  volatile uint8_t *bp = (volatile uint8_t *)usbdev_buf_idtoaddr(ctx, buf);
  if (size > BUF_LENGTH) {
    size = BUF_LENGTH;
  }

  TRC_C('0' + ctctx->ctrlstate);
  switch (ctctx->ctrlstate) {
    case kCtIdle:
      // Waiting to be set up
      if (setup && (size == 8)) {
        int bmRequestType = bp[0];
        int bRequest = bp[1];
        int wValue = (bp[3] << 8) | bp[2];
        int wIndex = (bp[5] << 8) | bp[4];
        int wLength = (bp[7] << 8) | bp[6];
        TRC_C('0' + bRequest);

        ctctx->ctrlstate = setup_req(ctctx, ctx, buf, bmRequestType, bRequest,
                                     wValue, wIndex, wLength);
        if (ctctx->ctrlstate != kCtError) {
          return;
        }
      }
      break;

    case kCtStatOut:
      // Have sent some data, waiting STATUS stage
      if (!setup && (size == 0)) {
        ctctx->ctrlstate = kCtIdle;
        return;
      }
      // anything else is unexpected
      break;

    default:
      // Error
      break;
  }
  usbdev_set_ep0_stall(ctx, 1);  // send a STALL, will be cleared by the HW
  TRC_S("USB: unCT ");
  TRC_I((ctctx->ctrlstate << 24) | setup << 16 | size, 32);
  TRC_C(':');
  for (int i = 0; i < size; i++) {
    TRC_I(bp[i], 8);
    TRC_C(' ');
  }
  usbdev_buf_free_byid(ctx, buf);
  ctctx->ctrlstate = kCtIdle;
}

// Callback for the USB link reset
void ctrl_reset(void *ctctx_v) {
  usb_controlep_ctx_t *ctctx = (usb_controlep_ctx_t *)ctctx_v;
  ctctx->ctrlstate = kCtIdle;
}

void usb_controlep_init(usb_controlep_ctx_t *ctctx, usbdev_ctx_t *ctx, int ep,
                        const uint8_t *cfg_dscr, size_t cfg_dscr_len) {
  ctctx->ctx = ctx;
  usbdev_endpoint_setup(ctx, ep, 1, ctctx, ctrl_tx_done, ctrl_rx, NULL,
                        ctrl_reset);
  ctctx->ctrlstate = kCtIdle;
  ctctx->cfg_dscr = cfg_dscr;
  ctctx->cfg_dscr_len = cfg_dscr_len;
}
