// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
#include "usbdpi.h"

// DPI test numbers
typedef enum usb_testutils_test_number {
  kUsbTestNumberSmoke = 0,
  kUsbTestNumberStreams,
  kUsbTestNumberIso,
  kUsbTestNumberMixed
} usb_testutils_test_number_t;

// Test-specific initialization
void usbdpi_test_init(usbdpi_ctx_t *ctx);

// Return the next step in the test sequence
usbdpi_test_step_t usbdpi_test_seq_next(usbdpi_ctx_t *ctx,
                                        usbdpi_test_step_t step);

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USBDPI_TEST_H_
