// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/usb_testutils_controlep.h"

#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/usb_testutils.h"

// String IDentifiers defined by our device
#define STRINGID_VENDOR 0x01U
#define STRINGID_PRODUCT 0x02U
#define STRINGID_SERIAL 0x03U

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

    0,                 // bcdDevice[0]
    0x1,               // bcdDevice[1]
    STRINGID_VENDOR,   // iManufacturer
    STRINGID_PRODUCT,  // iProduct
    STRINGID_SERIAL,   // iSerialNumber
    1                  // bNumConfigurations
};

// SETUP requests
typedef enum usb_setup_req {
  kUsbSetupReqGetStatus = 0,
  kUsbSetupReqClearFeature = 1,
  kUsbSetupReqSetFeature = 3,
  kUsbSetupReqSetAddress = 5,
  kUsbSetupReqGetDescriptor = 6,
  kUsbSetupReqSetDescriptor = 7,
  kUsbSetupReqGetConfiguration = 8,
  kUsbSetupReqSetConfiguration = 9,
  kUsbSetupReqGetInterface = 10,
  kUsbSetupReqSetInterface = 11,
  kUsbSetupReqSynchFrame = 12
} usb_setup_req_t;

// Vendor-specific requests defined by our device/test framework
typedef enum vendor_setup_req {
  kVendorSetupReqTestConfig = 0x7C,
  kVendorSetupReqTestStatus = 0x7E
} vendor_setup_req_t;

typedef enum usb_req_type {  // bmRequestType
  kUsbReqTypeRecipientMask = 0x1f,
  kUsbReqTypeDevice = 0,
  kUsbReqTypeInterface = 1,
  kUsbReqTypeEndpoint = 2,
  kUsbReqTypeOther = 3,
  kUsbReqTypeTypeMask = 0x60,
  kUsbReqTypeStandard = 0,
  kUsbReqTypeClass = 0x20,
  kUsbReqTypeVendor = 0x40,
  kUsbReqTypeReserved = 0x60,
  kUsbReqTypeDirMask = 0x80,
  kUsbReqTypeDirH2D = 0x00,
  kUsbReqTypeDirD2H = 0x80,
} usb_req_type_t;

typedef enum usb_desc_type {  // Descriptor type (wValue hi)
  kUsbDescTypeDevice = 1,
  kUsbDescTypeConfiguration,
  kUsbDescTypeString,
  kUsbDescTypeInterface,
  kUsbDescTypeEndpoint,
  kUsbDescTypeDeviceQualifier,
  kUsbDescTypeOtherSpeedConfiguration,
  kUsbDescTypeInterfacePower,
} usb_desc_type_t;

typedef enum usb_feature_req {
  kUsbFeatureEndpointHalt = 0,        // recipient is endpoint
  kUsbFeatureDeviceRemoteWakeup = 1,  // recipient is device
  kUsbFeatureTestMode = 2,            // recipient is device
  kUsbFeatureBHnpEnable = 3,          // recipient is device only if OTG
  kUsbFeatureAHnpSupport = 4,         // recipient is device only if OTG
  kUsbFeatureAAltHnpSupport = 5       // recipient is device only if OTG
} usb_feature_req_t;

typedef enum usb_status {
  kUsbStatusSelfPowered = 1,  // Device status request
  kUsbStatusRemWake = 2,      // Device status request
  kUsbStatusHalted = 1        // Endpoint status request
} usb_status_t;

#define USB_STR_DSCR(idx, string)                   \
  {                                                 \
    .length = (sizeof(string) + 1), .index = (idx), \
    .text = (uint8_t *)(string)                     \
  }

typedef struct usb_string {
  uint8_t length;
  uint8_t index;
  const uint8_t *text;
} usb_string_t;

// TODO - it should probably be the responsibility of the client software to
// specify the string table; this just gives us a bit more visibility
static const usb_string_t string_table[] = {
    // Unicode 16-bit wide characters
    // lowRISC C.I.C.
    USB_STR_DSCR(STRINGID_VENDOR, "l\0o\0w\0R\0I\0S\0C\0 \0C\0.\0I\0.\0C\0.\0"),
    // OpenTitan
    USB_STR_DSCR(STRINGID_PRODUCT, "O\0p\0e\0n\0T\0i\0t\0a\0n\0"),
    // CW-310
    USB_STR_DSCR(STRINGID_SERIAL, "C\0W\0-\0\x33\0\x31\0\x30\0"),
};

static usb_testutils_ctstate_t setup_req(usb_testutils_controlep_ctx_t *ctctx,
                                         usb_testutils_ctx_t *ctx,
                                         int bmRequestType, int bRequest,
                                         int wValue, int wIndex, int wLength) {
  const uint8_t *dscr;
  size_t dscr_len;
  size_t len;
  uint32_t stat;
  int zero, type;
  size_t bytes_written;
  // Endpoint for SetFeature/ClearFeature/GetStatus requests
  dif_usbdev_endpoint_id_t endpoint = {
      .number = (uint8_t)wIndex,
      .direction = bmRequestType & 0x80,
  };
  dif_usbdev_buffer_t buffer;
  CHECK_DIF_OK(dif_usbdev_buffer_request(ctx->dev, ctx->buffer_pool, &buffer));
  switch (bRequest) {
    case kUsbSetupReqGetDescriptor:
      TRC_S("GD");
      TRC_I(wValue, 16);
      switch ((wValue & 0xff00) >> 8) {
        case kUsbDescTypeDevice:
          // Device descriptor
          dscr_len = sizeof(dev_dscr);
          dscr = dev_dscr;
          break;
        case kUsbDescTypeConfiguration:
          // Configuration descriptor
          dscr = ctctx->cfg_dscr;
          dscr_len = ctctx->cfg_dscr_len;
          break;
        case kUsbDescTypeString:
          if ((uint8_t)wValue) {
            // String descriptor
            switch (wIndex) {
              case 0x409U:
              case 0x809U: {
                const unsigned nstrings =
                    sizeof(string_table) / sizeof(string_table[0]);
                unsigned idx = 0U;
                while (idx < nstrings &&
                       string_table[idx].index != (uint8_t)wValue) {
                  idx++;
                }
                if (idx < nstrings) {
                  uint8_t len = string_table[idx].length;
                  uint8_t data[2];
                  data[0] = len;
                  data[1] = kUsbDescTypeString;
                  CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, data,
                                                       2U, &bytes_written));
                  CHECK(bytes_written == 2U);
                  CHECK_DIF_OK(dif_usbdev_buffer_write(
                      ctx->dev, &buffer, string_table[idx].text, len - 2U,
                      &bytes_written));
                  CHECK(bytes_written == len - 2U);
                  CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
                  return kUsbTestutilsCtWaitIn;
                }
              } break;
            }
          } else {
            // List of supported LANGIDs
            uint8_t data[4];
            data[0] = 4;
            data[1] = kUsbDescTypeString;
            data[2] = 0x09;
            data[3] = 0x08;
            CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, data, 4,
                                                 &bytes_written));
            CHECK(bytes_written == 4);
            CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
            return kUsbTestutilsCtWaitIn;
          }
          break;
        // case kUsbDescTypeDeviceQualifier:
        // no break
        default:
          return kUsbTestutilsCtError;  // unknown
      }

      // Ensure that we do not send more than requested
      if (wLength < dscr_len) {
        dscr_len = wLength;
      }

      // Number of bytes in first buffer
      len = dscr_len;
      if (len >= buffer.remaining_bytes) {
        len = buffer.remaining_bytes;
      }

      bool max_packet = (len >= buffer.remaining_bytes);
      CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, dscr, len,
                                           &bytes_written));
      CHECK(bytes_written == len);
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtWaitIn;

    case kUsbSetupReqSetAddress:
      TRC_S("SA");
      ctctx->new_dev = wValue & 0x7f;
      // send zero length packet for status phase
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtAddrStatIn;

    case kUsbSetupReqSetConfiguration:
      TRC_S("SC");
      // only ever expect this to be 1 since there is one config descriptor
      ctctx->usb_config = wValue;
      // send zero length packet for status phase
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      if (wValue) {
        ctctx->device_state = kUsbTestutilsDeviceConfigured;
      } else {
        // Device deconfigured
        ctctx->device_state = kUsbTestutilsDeviceAddressed;
      }
      return kUsbTestutilsCtStatIn;

    case kUsbSetupReqGetConfiguration:
      len = sizeof(ctctx->usb_config);
      if (wLength < len) {
        len = wLength;
      }
      // return the value that was set
      CHECK_DIF_OK(dif_usbdev_buffer_write(
          ctx->dev, &buffer, &ctctx->usb_config, len, &bytes_written));
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtWaitIn;

    case kUsbSetupReqSetFeature:
      if (wValue == kUsbFeatureEndpointHalt) {
        CHECK_DIF_OK(dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint,
                                                      kDifToggleEnabled));
        // send zero length packet for status phase
        CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
        return kUsbTestutilsCtStatIn;
      }
      return kUsbTestutilsCtError;  // unknown

    case kUsbSetupReqClearFeature:
      if (wValue == kUsbFeatureEndpointHalt) {
        CHECK_DIF_OK(dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint,
                                                      kDifToggleDisabled));
        // send zero length packet for status phase
        CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      }
      return kUsbTestutilsCtStatIn;

    case kUsbSetupReqGetStatus:
      len = 2;
      type = bmRequestType & kUsbReqTypeRecipientMask;
      if (type == kUsbReqTypeDevice) {
        stat = kUsbStatusSelfPowered;
      } else if (type == kUsbReqTypeEndpoint) {
        bool halted;
        CHECK_DIF_OK(
            dif_usbdev_endpoint_stall_get(ctx->dev, endpoint, &halted));
        stat = halted ? kUsbStatusHalted : 0;
      } else {
        stat = 0;
      }
      if (wLength < len) {
        len = wLength;
      }
      // return the value that was set
      CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, (uint8_t *)&stat,
                                           len, &bytes_written));
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtWaitIn;

    case kUsbSetupReqSetInterface:
      // Don't support alternate interfaces, so just ignore
      // send zero length packet for status phase
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtStatIn;

    case kUsbSetupReqGetInterface:
      zero = 0;
      len = 1;
      if (wLength < len) {
        len = wLength;
      }
      // Don't support interface, so return zero
      CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, (uint8_t *)&zero,
                                           len, &bytes_written));
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtWaitIn;

    case kUsbSetupReqSynchFrame:
      zero = 0;
      len = 2;
      if (wLength < len) {
        len = wLength;
      }
      // Don't support synch_frame so return zero
      CHECK_DIF_OK(dif_usbdev_buffer_write(ctx->dev, &buffer, (uint8_t *)&zero,
                                           len, &bytes_written));
      CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
      return kUsbTestutilsCtWaitIn;

    default:
      // We implement a couple of bespoke, vendor-defined Setup requests to
      // allow the DPI model to access the test configuration (Control Read) and
      // to report the test status (Control Write)
      if ((bmRequestType & kUsbReqTypeTypeMask) == kUsbReqTypeVendor &&
          ctctx->test_dscr) {
        switch ((vendor_setup_req_t)bRequest) {
          case kVendorSetupReqTestConfig: {
            TRC_S("TC");
            // Test config descriptor
            len = ctctx->test_dscr_len;
            if (wLength < len) {
              len = wLength;
            }
            CHECK_DIF_OK(dif_usbdev_buffer_write(
                ctx->dev, &buffer, ctctx->test_dscr, len, &bytes_written));
            CHECK_DIF_OK(dif_usbdev_send(ctx->dev, ctctx->ep, &buffer));
            return kUsbTestutilsCtWaitIn;
          } break;
          case kVendorSetupReqTestStatus: {
            // TODO - pass the received test status to the OTTF directly?
          } break;
        }
      }
      return kUsbTestutilsCtError;
  }
  return kUsbTestutilsCtError;
}

static void ctrl_tx_done(void *ctctx_v) {
  usb_testutils_controlep_ctx_t *ctctx =
      (usb_testutils_controlep_ctx_t *)ctctx_v;
  usb_testutils_ctx_t *ctx = ctctx->ctx;
  TRC_C('A' + ctctx->ctrlstate);
  switch (ctctx->ctrlstate) {
    case kUsbTestutilsCtAddrStatIn:
      // Now the status was sent on device 0 can switch to new device ID
      CHECK_DIF_OK(dif_usbdev_address_set(ctx->dev, ctctx->new_dev));
      TRC_I(ctctx->new_dev, 8);
      ctctx->ctrlstate = kUsbTestutilsCtIdle;
      // We now have a device address on the USB
      ctctx->device_state = kUsbTestutilsDeviceAddressed;
      return;
    case kUsbTestutilsCtStatIn:
      ctctx->ctrlstate = kUsbTestutilsCtIdle;
      return;
    case kUsbTestutilsCtWaitIn:
      ctctx->ctrlstate = kUsbTestutilsCtStatOut;
      return;

    default:
      break;
  }
  TRC_S("USB: unexpected IN ");
  TRC_I((ctctx->ctrlstate << 24), 32);
}

static void ctrl_rx(void *ctctx_v, dif_usbdev_rx_packet_info_t packet_info,
                    dif_usbdev_buffer_t buffer) {
  usb_testutils_controlep_ctx_t *ctctx =
      (usb_testutils_controlep_ctx_t *)ctctx_v;
  usb_testutils_ctx_t *ctx = ctctx->ctx;
  CHECK_DIF_OK(dif_usbdev_endpoint_out_enable(ctx->dev, /*endpoint=*/0,
                                              kDifToggleEnabled));

  TRC_C('0' + ctctx->ctrlstate);
  uint32_t bytes_written;
  // TODO: Should check for canceled IN transactions due to receiving a SETUP
  // packet.
  switch (ctctx->ctrlstate) {
    case kUsbTestutilsCtIdle:
      // Waiting to be set up
      if (packet_info.is_setup && (packet_info.length == 8)) {
        alignas(uint32_t) uint8_t bp[8];
        CHECK_DIF_OK(dif_usbdev_buffer_read(ctx->dev, ctx->buffer_pool, &buffer,
                                            bp, sizeof(bp), &bytes_written));
        int bmRequestType = bp[0];
        int bRequest = bp[1];
        int wValue = (bp[3] << 8) | bp[2];
        int wIndex = (bp[5] << 8) | bp[4];
        int wLength = (bp[7] << 8) | bp[6];
        TRC_C('0' + bRequest);

        ctctx->ctrlstate = setup_req(ctctx, ctx, bmRequestType, bRequest,
                                     wValue, wIndex, wLength);
        if (ctctx->ctrlstate != kUsbTestutilsCtError) {
          return;
        }

        TRC_C(':');
        for (int i = 0; i < packet_info.length; i++) {
          TRC_I(bp[i], 8);
        }
      }
      break;

    case kUsbTestutilsCtStatOut:
      // Have sent some data, waiting STATUS stage
      if (!packet_info.is_setup && (packet_info.length == 0)) {
        CHECK_DIF_OK(
            dif_usbdev_buffer_return(ctx->dev, ctx->buffer_pool, &buffer));
        ctctx->ctrlstate = kUsbTestutilsCtIdle;
        return;
      }
      // anything else is unexpected
      break;

    default:
      // Error
      break;
  }
  dif_usbdev_endpoint_id_t endpoint = {
      .number = 0,
      .direction = USBDEV_ENDPOINT_DIR_IN,
  };
  // Enable responding with STALL. Will be cleared by the HW.
  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleEnabled));
  endpoint.direction = USBDEV_ENDPOINT_DIR_OUT;
  CHECK_DIF_OK(
      dif_usbdev_endpoint_stall_enable(ctx->dev, endpoint, kDifToggleEnabled));
  TRC_S("USB: unCT ");
  TRC_I((ctctx->ctrlstate << 24) | ((int)packet_info.is_setup << 16) |
            packet_info.length,
        32);
  if (buffer.type != kDifUsbdevBufferTypeStale) {
    // Return the unused buffer.
    CHECK_DIF_OK(dif_usbdev_buffer_return(ctx->dev, ctx->buffer_pool, &buffer));
  }
  ctctx->ctrlstate = kUsbTestutilsCtIdle;
}

// Callback for the USB link reset
static void ctrl_reset(void *ctctx_v) {
  usb_testutils_controlep_ctx_t *ctctx =
      (usb_testutils_controlep_ctx_t *)ctctx_v;
  ctctx->ctrlstate = kUsbTestutilsCtIdle;
}

void usb_testutils_controlep_init(usb_testutils_controlep_ctx_t *ctctx,
                                  usb_testutils_ctx_t *ctx, int ep,
                                  const uint8_t *cfg_dscr, size_t cfg_dscr_len,
                                  const uint8_t *test_dscr,
                                  size_t test_dscr_len) {
  ctctx->ctx = ctx;
  usb_testutils_endpoint_setup(ctx, ep, kUsbdevOutMessage, ctctx, ctrl_tx_done,
                               ctrl_rx, NULL, ctrl_reset);
  ctctx->ep = ep;
  ctctx->ctrlstate = kUsbTestutilsCtIdle;
  ctctx->cfg_dscr = cfg_dscr;
  ctctx->cfg_dscr_len = cfg_dscr_len;
  ctctx->test_dscr = test_dscr;
  ctctx->test_dscr_len = test_dscr_len;
  CHECK_DIF_OK(dif_usbdev_interface_enable(ctx->dev, kDifToggleEnabled));
  ctctx->device_state = kUsbTestutilsDeviceDefault;
}
