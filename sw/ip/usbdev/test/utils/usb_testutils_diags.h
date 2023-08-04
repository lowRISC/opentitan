// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
// Diagnostic, testing and performance measurements utilities for verification
// of usbdev and development of the usb_testutils support software; the
// requirements of this software are peculiar in that the USBDPI model used in
// top-level requires packet responses very promptly, so the introduction of
// logging/tracing code can substantially alter behavior and cause malfunction
//
// Employ faster memory copying routines to/from the packet buffer
//   (the standard dif_usbdev_buffer_write/read functionality should normally be
//    employed, but it is inefficient; the replacement routines better model the
//    attainable performance)
#ifndef USBUTILS_MEM_FASTER
#define USBUTILS_MEM_FASTER 1
#endif

// Used for tracing what is going on. This may impact timing which is critical
// when simulating with the USB DPI module.
#define USBUTILS_ENABLE_TRC 0

#if USBUTILS_ENABLE_TRC
// May be useful on FPGA CW310
#include "sw/device/lib/runtime/log.h"
#define TRC_S(s) LOG_INFO("%s", s)
#define TRC_I(i, b) LOG_INFO("0x%x", i)
#define TRC_C(c) LOG_INFO("%c", c)
#else
#define TRC_S(s)
#define TRC_I(i, b)
#define TRC_C(c)
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
