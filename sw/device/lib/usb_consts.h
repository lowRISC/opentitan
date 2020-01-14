// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_USB_CONSTS_H_
#define OPENTITAN_SW_DEVICE_LIB_USB_CONSTS_H_

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
  KUsbReqTypeStandard = 0,
  KUsbReqTypeClass = 0x20,
  KUsbReqTypeVendor = 0x40,
  KUsbReqTypeReserved = 0x60,
  kUsbReqTypeDirMask = 0x80,
  kUsbReqTypeDirH2D = 0x00,
  kUsbReqTypeDirD2H = 0x80,
} usb_req_type_t;

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

#endif  // OPENTITAN_SW_DEVICE_LIB_USB_CONSTS_H_
