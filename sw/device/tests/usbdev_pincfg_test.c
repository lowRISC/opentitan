// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB pincfg test
//
// For each of the pin/bus configurations in turn, this test runs the USB test
// software, device and DPI model through all of the initial communications to
// set up the device and select a confgiguration.
//
// It is necessary to perform a complete reset of the usbdev hardware block
// before starting the next test because the DIF keeps the 'Available buffers'
// FIFO topped up with buffers, but would itself forget about those buffers
// when reinitialized for the next test.
//
// This test works best with the DPI model in Verilator top-level simulation
// because it is capable of reading and adapting to the pin configuration and
// thus implementing all bus types:
//
// - differential vs single-ended, in each direction
// - pin-swapped vs unswapped
//
// With DV sim at chip level, where we have just the physical two wire USB
// between the chip and DPI model, 4 configurations may be exercised.
//
// On the CW310/340 target, only two configurations may be tested
// programmatically without the manual intervention required to flip pins. No
// host-side application support is required in this case - just a physical wire
// to the host controller, and the OS/device layer will configure the device.

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
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
static const uint8_t kConfigDescriptors[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + 2 * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN),
        2),
    VEND_INTERFACE_DSCR(0, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 1, 32, 0),
    USB_BULK_EP_DSCR(1, 1, 32, 4),
    VEND_INTERFACE_DSCR(1, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 2, 32, 0),
    USB_BULK_EP_DSCR(1, 2, 32, 4),
};

/**
 * Test descriptor
 */
static const uint8_t kTestDescriptor[] = {
    USB_TESTUTILS_TEST_DSCR(kUsbTestNumberPinCfg, 0, 0, 0, 0)};

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

/**
 * Rstmgr handler
 */
static dif_rstmgr_t rstmgr;

/**
 * Verbose reporting?
 */
static bool verbose = false;

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  LOG_INFO("Running USBDEV PINCFG test");

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Construct the test list appropriate to this target
  struct {
    bool pinflip;
    bool en_diff_rcvr;
    bool tx_use_d_se0;
  } test_cfg[8U];

  unsigned ntests;
  switch (kDeviceType) {
    case kDeviceSimDV:
      // DV simulation can exercise pin-flipping and differential rcvr on/off
      // but there's no point wasting simulation time trying both tx modes;
      // D+/D- are always used directly as differential signals.
      ntests = 4U;
      for (unsigned test = 0U; test < ntests; ++test) {
        test_cfg[test].pinflip = ((test & 1U) != 0U);
        test_cfg[test].en_diff_rcvr = ((test & 2U) != 0U);
        test_cfg[test].tx_use_d_se0 = false;
      }
      break;

    case kDeviceFpgaCw340:
    case kDeviceFpgaCw310:
      LOG_INFO(" - CW310/340 does not support pinflipping; ignoring");
      LOG_INFO(" - CW310/340 employs only differential transmission");
      ntests = 2U;
      for (unsigned test = 0U; test < ntests; ++test) {
        // For the CW310/340 pin-flipping is only useful if the SBU signals of
        // the USB-C connector are being driven; this is not the case we're
        // testing.
        test_cfg[test].pinflip = false;
        test_cfg[test].en_diff_rcvr = ((test & 1U) != 0U);
        // D+/D- signals are always used directly as differential signals.
        test_cfg[test].tx_use_d_se0 = false;
      }
      // Fine to employ verbose logging because behavior on FPGA is not
      // timing-sensitive.
      verbose = true;
      break;

    // Verilator can operate with any pin/bus configuration because it has
    // ready access to the configuration information.
    default:
      CHECK(kDeviceType == kDeviceSimVerilator);
      ntests = 8U;
      for (unsigned test = 0U; test < ntests; ++test) {
        test_cfg[test].pinflip = ((test & 1U) != 0U);
        test_cfg[test].en_diff_rcvr = ((test & 2U) != 0U);
        test_cfg[test].tx_use_d_se0 = ((test & 4U) != 0U);
      }
      break;
  }

  for (unsigned test = 0U; test < ntests; ++test) {
    bool tx_use_d_se0 = test_cfg[test].tx_use_d_se0;
    bool en_diff_rcvr = test_cfg[test].en_diff_rcvr;
    bool pinflip = test_cfg[test].pinflip;

    if (verbose) {
      LOG_INFO("Init test %u pinflip %!b en_diff_rcvr %!b tx_use_d_se0 %!b",
               test, pinflip, en_diff_rcvr, tx_use_d_se0);
    }

    // Note: this call will result in the buffer pool being (re)initialised and
    // as such it _would_ be in disagreement with the hardware if usbdev were
    // not reset after the previous test
    CHECK_STATUS_OK(
        usb_testutils_init(&usbdev, pinflip, en_diff_rcvr, tx_use_d_se0));

    // Set up the control endpoint and see that we enter the configured state,
    // implying successful communication between the DPI model and device
    CHECK_STATUS_OK(usb_testutils_controlep_init(
        &usbdev_control, &usbdev, 0, kConfigDescriptors,
        sizeof(kConfigDescriptors), kTestDescriptor, sizeof(kTestDescriptor)));

    // Configuration shall have been selected only after the host/DPI model has
    // successfully concluded the SET_CONFIGURATION control transfer
    const uint32_t kTimeoutUsecs = 30 * 1000000;
    ibex_timeout_t timeout = ibex_timeout_init(kTimeoutUsecs);
    while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured &&
           !ibex_timeout_check(&timeout)) {
      CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
    }
    // Check that we were configured, implying that communication is working.
    CHECK(usbdev_control.device_state == kUsbTestutilsDeviceConfigured);

    if (kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSimVerilator) {
      // TODO: We shall probably want simply to drop the connection and control
      // the DPI in time, as we do for the physical host at present.
      dif_usbdev_link_state_t link_state;
      do {
        CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
        CHECK_DIF_OK(dif_usbdev_status_get_link_state(usbdev.dev, &link_state));
      } while (link_state == kDifUsbdevLinkStateActive);
    }

    // Shut down the usb_testutils layer, in preparation for restarting;
    // this disconnects usbdev from the bus. The DPI model will detect this and
    // restart, awaiting a further connection attempt.
    CHECK_STATUS_OK(usb_testutils_fin(&usbdev));

    // We must force a reset of the entire usbdev block in order to perform
    // the next test successfully, because otherwise buffers remain in the
    // internal FIFOs
    if (verbose) {
      LOG_INFO(" - Hold reset");
    }
    CHECK_DIF_OK(dif_rstmgr_software_reset(&rstmgr,
                                           kTopEarlgreyResetManagerSwResetsUsb,
                                           kDifRstmgrSoftwareResetHold));
    if (verbose) {
      LOG_INFO(" - Release reset");
    }
    CHECK_DIF_OK(dif_rstmgr_software_reset(&rstmgr,
                                           kTopEarlgreyResetManagerSwResetsUsb,
                                           kDifRstmgrSoftwareResetRelease));
  }

  return true;
}
