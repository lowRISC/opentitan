// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_H_

#include <stdint.h>

typedef enum dt_device {
  kDtDeviceUnknown = 0,
  kDtDeviceAdcCtrl,
  kDtDeviceAes,
  kDtDeviceAonTimer,
  kDtDeviceClkmgr,
  kDtDeviceCsrng,
  kDtDeviceEdn,
  kDtDeviceEntropySrc,
  kDtDeviceFlashCtrl,
  kDtDeviceGpio,
  kDtDeviceHmac,
  kDtDeviceI2c,
  kDtDeviceKeymgr,
  kDtDeviceKmac,
  kDtDeviceLcCtrl,
  kDtDeviceOtbn,
  kDtDeviceOtpCtrl,
  kDtDevicePattgen,
  kDtDevicePinmux,
  kDtDevicePwm,
  kDtDeviceRomCtrl,
  kDtDeviceRstmgr,
  kDtDeviceRvCoreIbex,
  kDtDeviceRvDm,
  kDtDeviceRvTimer,
  kDtDeviceSpiDevice,
  kDtDeviceSpiHost,
  kDtDeviceSramCtrl,
  kDtDeviceSysrstCtrl,
  kDtDeviceUart,
  kDtDeviceUsbdev,
} dt_device_t;

extern uintptr_t dt_reg_addr(dt_device_t dev, uint32_t dev_idx,
                             uint32_t reg_iface_idx);

// Need chosen devices to deal with unpredictability of the ordering. This will
// help patch up which UART is to be used for the console (for example).
#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_H_
