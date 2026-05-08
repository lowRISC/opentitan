// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_STDUSB_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_STDUSB_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

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
  kUsbReqTypeDirHostToDev = 0x00,
  kUsbReqTypeDirDevToHost = 0x80,
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

typedef struct usb_setup_data {
  uint8_t request_type;
  uint8_t request;
  uint16_t value;
  uint16_t index;
  uint16_t length;
} usb_setup_data_t;
OT_ASSERT_MEMBER_OFFSET(usb_setup_data_t, request_type, 0);
OT_ASSERT_MEMBER_OFFSET(usb_setup_data_t, request, 1);
OT_ASSERT_MEMBER_OFFSET(usb_setup_data_t, value, 2);
OT_ASSERT_MEMBER_OFFSET(usb_setup_data_t, index, 4);
OT_ASSERT_MEMBER_OFFSET(usb_setup_data_t, length, 6);
OT_ASSERT_SIZE(usb_setup_data_t, 8);

typedef struct usb_device_descriptor {
  uint8_t length;
  uint8_t descriptor_type;
  uint16_t bcd_usb;
  uint8_t device_class;
  uint8_t device_sub_class;
  uint8_t device_protocol;
  uint8_t max_packet_size_0;
  uint16_t vendor;
  uint16_t product;
  uint16_t bcd_device;
  uint8_t imanufacturer;
  uint8_t iproduct;
  uint8_t iserial_number;
  uint8_t num_configurations;
} usb_device_descriptor_t;

typedef struct usb_configuration_descriptor {
  uint8_t length;
  uint8_t descriptor_type;
  uint16_t total_length;
  uint8_t num_interfaces;
  uint8_t configuration_value;
  uint8_t iconfiguration;
  uint8_t attributes;
  uint8_t max_power;
} usb_configuration_descriptor_t;

typedef struct usb_interface_descriptor {
  uint8_t length;
  uint8_t descriptor_type;
  uint8_t interface_number;
  uint8_t alternate_setting;
  uint8_t num_endpoints;
  uint8_t interface_class;
  uint8_t interface_sub_class;
  uint8_t interface_protocol;
  uint8_t iinterface;
} usb_interface_descriptor_t;

typedef struct usb_endpoint_descriptor {
  uint8_t length;
  uint8_t descriptor_type;
  uint8_t endpoint_address;
  uint8_t attributes;
  uint16_t max_packet_size;
  uint8_t interval;
} usb_endpoint_descriptor_t;

typedef struct usb_string_descriptor {
  uint8_t length;
  uint8_t descriptor_type;
  uint16_t string[];
} usb_string_descriptor_t;

typedef enum usb_control_flags {
  kUsbControlFlagsPendingAddress = 1,
  kUsbControlFlagsPendingConfig = 2,
} usb_control_flags_t;

typedef struct usb_control_ctx {
  usb_control_flags_t flags;
  uint8_t device_address;
  uint8_t configuration;
  struct {
    uint8_t device_address;
    uint8_t configuration;
  } next;
  const usb_device_descriptor_t *device_desc;
  const uint8_t *config_desc;
  const char **string_desc;
} usb_control_ctx_t;

/**
 * Handle standard USB requests for endpoint zero.
 *
 * @param ctx A pointer to a usb_control_ctx_t.
 * @param setup A pointer to a SETUPDATA request to process.
 * @return kErrorOk if handled, kErrorUsbBadSetup if a stall is needed.
 *
 * Notes: The caller has responsibilities upon observing certain bits
 * set in usb_control_flags_t.
 *
 * 1. If you observe kUsbControlFlagsPendingAddress, you need to set the device
 *    address in your control endpoint callback after the control transaction
 *    has completed (e.g. `kUsbTransferFlagsDone`).
 *
 * 2. If you observe kUsbControlFlagsPendingConfig, you need to transition to
 *    the new configuration in your control endpoint callback and finish the
 *    control transaction.
 *    - If you're able to handle the SetConfiguration request without
 *      error, you must ack the transaction with a zero-length packet,
 *      such as: `usb_ep_transfer(0, NULL, 0, kUsbTransferFlagsIn)
 *    - If you're unable to handle the SetConfiguration request,
 *      you must stall: `usb_ep_stall(0)`.
 */
rom_error_t usb_control_setupdata(usb_control_ctx_t *ctx,
                                  usb_setup_data_t *setup);

/**
 * Macros to help with constructing the config descriptor.
 */
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
#define USB_INTERFACE_DSCR(inum, alt, nep, class_, subclass, protocol, iint)   \
  /* interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12 */         \
  USB_INTERFACE_DSCR_LEN,            /* bLength                             */ \
      4,                             /* bDescriptorType                     */ \
      (inum),                        /* bInterfaceNumber                    */ \
      (alt),                         /* bAlternateSetting                   */ \
      (nep),                         /* bNumEndpoints                       */ \
      (class_),                      /* bInterfaceClass (Vendor Specific)   */ \
      (subclass),                    /* bInterfaceSubClass                  */ \
      (protocol),                    /* bInterfaceProtocol                  */ \
      (iint) /* iInterface        */ /* MUST be followed by                    \
                                        (nep) Endpoint                         \
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

/**
 * A macro to help with constructing small (less than 32 chars) string
 * descriptors.
 */
#define USB_STRING_DSCR(...)                                        \
  2 + OT_VA_ARGS_COUNT(dummy, ##__VA_ARGS__) * 2,                   \
      3 /* Missing comma intentional */                             \
      OT_CAT(OT_CAT(USB_CHAR_, OT_VA_ARGS_COUNT(0, ##__VA_ARGS__)), \
             _)(__VA_ARGS__)

#define USB_CHAR_1_(x) , x, 0
#define USB_CHAR_2_(x, ...) , x, 0 USB_CHAR_1_(__VA_ARGS__)
#define USB_CHAR_3_(x, ...) , x, 0 USB_CHAR_2_(__VA_ARGS__)
#define USB_CHAR_4_(x, ...) , x, 0 USB_CHAR_3_(__VA_ARGS__)
#define USB_CHAR_5_(x, ...) , x, 0 USB_CHAR_4_(__VA_ARGS__)
#define USB_CHAR_6_(x, ...) , x, 0 USB_CHAR_5_(__VA_ARGS__)
#define USB_CHAR_7_(x, ...) , x, 0 USB_CHAR_6_(__VA_ARGS__)
#define USB_CHAR_8_(x, ...) , x, 0 USB_CHAR_7_(__VA_ARGS__)
#define USB_CHAR_9_(x, ...) , x, 0 USB_CHAR_8_(__VA_ARGS__)
#define USB_CHAR_10_(x, ...) , x, 0 USB_CHAR_9_(__VA_ARGS__)
#define USB_CHAR_11_(x, ...) , x, 0 USB_CHAR_10_(__VA_ARGS__)
#define USB_CHAR_12_(x, ...) , x, 0 USB_CHAR_11_(__VA_ARGS__)
#define USB_CHAR_13_(x, ...) , x, 0 USB_CHAR_12_(__VA_ARGS__)
#define USB_CHAR_14_(x, ...) , x, 0 USB_CHAR_13_(__VA_ARGS__)
#define USB_CHAR_15_(x, ...) , x, 0 USB_CHAR_14_(__VA_ARGS__)
#define USB_CHAR_16_(x, ...) , x, 0 USB_CHAR_15_(__VA_ARGS__)
#define USB_CHAR_17_(x, ...) , x, 0 USB_CHAR_16_(__VA_ARGS__)
#define USB_CHAR_18_(x, ...) , x, 0 USB_CHAR_17_(__VA_ARGS__)
#define USB_CHAR_19_(x, ...) , x, 0 USB_CHAR_18_(__VA_ARGS__)
#define USB_CHAR_20_(x, ...) , x, 0 USB_CHAR_19_(__VA_ARGS__)
#define USB_CHAR_21_(x, ...) , x, 0 USB_CHAR_20_(__VA_ARGS__)
#define USB_CHAR_22_(x, ...) , x, 0 USB_CHAR_21_(__VA_ARGS__)
#define USB_CHAR_23_(x, ...) , x, 0 USB_CHAR_22_(__VA_ARGS__)
#define USB_CHAR_24_(x, ...) , x, 0 USB_CHAR_23_(__VA_ARGS__)
#define USB_CHAR_25_(x, ...) , x, 0 USB_CHAR_24_(__VA_ARGS__)
#define USB_CHAR_26_(x, ...) , x, 0 USB_CHAR_25_(__VA_ARGS__)
#define USB_CHAR_27_(x, ...) , x, 0 USB_CHAR_26_(__VA_ARGS__)
#define USB_CHAR_28_(x, ...) , x, 0 USB_CHAR_27_(__VA_ARGS__)
#define USB_CHAR_29_(x, ...) , x, 0 USB_CHAR_28_(__VA_ARGS__)
#define USB_CHAR_30_(x, ...) , x, 0 USB_CHAR_29_(__VA_ARGS__)
#define USB_CHAR_31_(x, ...) , x, 0 USB_CHAR_30_(__VA_ARGS__)
#define USB_CHAR_32_(x, ...) , x, 0 USB_CHAR_31_(__VA_ARGS__)

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_STDUSB_H_
