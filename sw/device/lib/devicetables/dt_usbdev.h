// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_USBDEV_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_USBDEV_H_

#include <stdint.h>

#include "sw/device/lib/devicetables/dt.h"

typedef enum {
  kDtUsbdevRegBlockCore = 0,
  kDtUsbdevRegBlockCount = 1,
} dt_usbdev_reg_block_t;

typedef enum {
  kDtUsbdevIrqTypePktReceived = 0,
  kDtUsbdevIrqTypePktSent = 1,
  kDtUsbdevIrqTypeDisconnected = 2,
  kDtUsbdevIrqTypeHostLost = 3,
  kDtUsbdevIrqTypeLinkReset = 4,
  kDtUsbdevIrqTypeLinkSuspend = 5,
  kDtUsbdevIrqTypeLinkResume = 6,
  kDtUsbdevIrqTypeAvOutEmpty = 7,
  kDtUsbdevIrqTypeRxFull = 8,
  kDtUsbdevIrqTypeAvOverflow = 9,
  kDtUsbdevIrqTypeLinkInErr = 10,
  kDtUsbdevIrqTypeRxCrcErr = 11,
  kDtUsbdevIrqTypeRxPidErr = 12,
  kDtUsbdevIrqTypeRxBitstuffErr = 13,
  kDtUsbdevIrqTypeFrame = 14,
  kDtUsbdevIrqTypePowered = 15,
  kDtUsbdevIrqTypeLinkOutErr = 16,
  kDtUsbdevIrqTypeAvSetupEmpty = 17,
  kDtUsbdevIrqTypeCount = 18,
} dt_usbdev_irq_type_t;

typedef enum {
  kDtUsbdevClockClk = 0,
  kDtUsbdevClockAon = 1,
  kDtUsbdevClockCount = 2,
} dt_usbdev_clock_t;

typedef enum {
  kDtUsbdevPinctrlInputSense = 0,
  kDtUsbdevPinctrlInoutUsbDp = 1,
  kDtUsbdevPinctrlInoutUsbDn = 2,
  kDtUsbdevPinctrlInputCount = 3,
  kDtUsbdevPinctrlOutputCount = 3,
} dt_usbdev_pinctrl_t;

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETABLES_DT_USBDEV_H_
