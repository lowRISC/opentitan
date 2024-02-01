// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB CONFIG HOST test
//
// Test basic configuration of the USB device by the host/DPI.
//
// It requires interaction with the USB DPI model or a physical host in order
// to receive and respond to the Control Transfers that are involved in the
// identification and configuration of the device.
//
// The test configures USB Endpoint 1 as a simpleserial endpoint which should
// appear as /dev/ttyUSBx on a Linux-based host.

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/usb_testutils.h"
#include "sw/device/lib/testing/usb_testutils_controlep.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

/**
 * Configuration values for USB.
 */
static const uint8_t config_descriptors[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN, 1),
    // Single interface...
    VEND_INTERFACE_DSCR(0, 1, 0x50, 1),
    // ... describing two Endpoints; endpoint 1 OUT and endpoint 1 IN
    USB_BULK_EP_DSCR(0, 1, 32, 0),
    USB_BULK_EP_DSCR(1, 1, 32, 4),
};

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // In simulation the DPI model connects VBUS shortly after reset and
  // prolonged delays when asserting or deasserting pull ups are wasteful.
  uint32_t timeout_micros = 6000u;
  bool prompt = false;

  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    // FPGA platforms where user intervention may be required.
    timeout_micros = 30 * 1000 * 1000u;
    // Report instructions/progress to user, when driven manually.
    prompt = true;
    LOG_INFO("Running USBDEV_CONFIG_HOST test");
    LOG_INFO("Awaiting configuration from the host");
  }

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // Call `usbdev_init` here so that DPI will not start until the
  // simulation has finished all of the printing, which takes a while
  // if `--trace` was passed in.
  CHECK_STATUS_OK(usb_testutils_init(&usbdev, /*pinflip=*/false,
                                     /*en_diff_rcvr=*/true,
                                     /*tx_use_d_se0=*/false));
  CHECK_STATUS_OK(usb_testutils_controlep_init(
      &usbdev_control, &usbdev, 0, config_descriptors,
      sizeof(config_descriptors), NULL, 0));

  // Proceed only when the device has been configured; this allows host-side
  // software to establish communication.
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured &&
         !ibex_timeout_check(&timeout)) {
    CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
  }

  bool success = (usbdev_control.device_state == kUsbTestutilsDeviceConfigured);
  if (success && prompt) {
    LOG_INFO("Configuration received");
  }
  CHECK(success);

  CHECK_STATUS_OK(usb_testutils_fin(&usbdev));

  return true;
}
