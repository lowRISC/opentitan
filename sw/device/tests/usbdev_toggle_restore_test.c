// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Device Toggle Restore test
//
// This is a simple test to exercise the ability to save and restore the
// Data Toggle bits within the USB device. That is important for resuming
// communication with the USB host controller after returning from a
// Deep Sleep state.
//
// Note that this test does not itself attempt to enter/resume from
// Deep Sleep.

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

/**
 * USB device handle
 */
static dif_usbdev_t usbdev;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

// Wait with timeout until the VBUS/SENSE signal is in the expected state.
static status_t vbus_wait(bool expected, uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Read the current state of VBUS.
    bool vbus;
    TRY(dif_usbdev_status_get_sense(&usbdev, &vbus));
    if (vbus == expected) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
}

// Wait with timeout until the link is in the expected state.
static status_t link_state_wait(dif_usbdev_link_state_t expected,
                                uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Read the current state of the link.
    dif_usbdev_link_state_t link_state;
    TRY(dif_usbdev_status_get_link_state(&usbdev, &link_state));
    if (link_state == expected) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
}

// Check that the data toggle bits read from the USB device match expectations.
static void check_toggles(uint16_t exp_out_toggles, uint16_t exp_in_toggles,
                          bool logging) {
  uint16_t act_out_toggles;
  uint16_t act_in_toggles;

  CHECK_DIF_OK(dif_usbdev_data_toggle_out_read(&usbdev, &act_out_toggles));
  CHECK_DIF_OK(dif_usbdev_data_toggle_in_read(&usbdev, &act_in_toggles));

  // Logging could cause this test to fail with the DPI in simulation and even
  // lead to flaky behaviour with a physical USB host controller because we
  // ignore the host for too long and it resorts to issuing a second Bus Reset.
  if (logging) {
    LOG_INFO("exp_out_toggles 0x%x act_out_toggles 0x%x", exp_out_toggles,
             act_out_toggles);
    LOG_INFO("exp_in_toggles 0x%x act_in_toggles 0x%x", exp_in_toggles,
             act_in_toggles);
  }

  CHECK(act_out_toggles == exp_out_toggles);
  CHECK(act_in_toggles == exp_in_toggles);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Mask defining the valid endpoints.
  const uint16_t all_endpoints = (uint16_t)(1u << USBDEV_NUM_ENDPOINTS) - 1u;
  // Expected state of the Data Toggle registers.
  uint16_t exp_out_toggles = (uint16_t)(0xAAAAu & all_endpoints);
  uint16_t exp_in_toggles = (uint16_t)(0x5555u & all_endpoints);
  uint32_t timeout_micros = 1000u;
  // Default to no prompting or logging.
  bool logging = false;
  bool prompt = false;

  switch (kDeviceType) {
    // In simulation the DPI model connects VBUS shortly after reset.
    case kDeviceSimDV:
      // logging is harmless for DV sim because of the `sw_logger_if` back door
      // reducing the simulation time.
      logging = true;
      OT_FALLTHROUGH_INTENDED;
    case kDeviceSimVerilator:
      // avoid logging with Verilator because it does not have the back door.
      timeout_micros = 1000u;
      break;
    default:
      // FPGA platforms where user intervention may be required.
      timeout_micros = 30 * 1000 * 1000u;
      prompt = true;
      // logging _may_ be used in this case but it could lead to flakiness,
      // through a failure to respond to the USB host controller promptly.
      logging = false;
      break;
  }

  // Ensure that the VBUS/SENSE signal is routed through to the usbdev
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));

  // Firstly, ensure that we are disconnected from the USB; if there's a
  // physical USB host controller cabled then this will force a reset of the
  // connection.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleDisabled));

  // Unfortunately we _do_ need to connect to the USB host controller/DPI model
  // to ensure that the link comes out of reset.
  bool vbus;
  CHECK_DIF_OK(dif_usbdev_status_get_sense(&usbdev, &vbus));
  if (!vbus) {
    if (prompt) {
      LOG_INFO("Connect or power up the USB");
    }
    CHECK_STATUS_OK(vbus_wait(true, timeout_micros));
  }

  // Now connect to the bus and wait for the link to come out of reset.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleEnabled));
  CHECK_STATUS_OK(
      link_state_wait(kDifUsbdevLinkStateActiveNoSof, timeout_micros));
  if (prompt) {
    LOG_INFO("Link out of reset; testing...");
  }

  // We must then quickly perform the testing before any communication from the
  // USB host controller occurs, because any communication will interfere with
  // the data toggle bits.

  // Set up a test pattern in the registers, putting all data toggle bits into
  // a defined state.
  CHECK_DIF_OK(dif_usbdev_data_toggle_out_write(&usbdev, all_endpoints,
                                                exp_out_toggles));
  CHECK_DIF_OK(
      dif_usbdev_data_toggle_in_write(&usbdev, all_endpoints, exp_in_toggles));

  // Check that they read as expected.
  check_toggles(exp_out_toggles, exp_in_toggles, logging);

  // Write an inverted test pattern.
  exp_out_toggles ^= all_endpoints;
  exp_in_toggles ^= all_endpoints;
  CHECK_DIF_OK(dif_usbdev_data_toggle_out_write(&usbdev, all_endpoints,
                                                exp_out_toggles));
  CHECK_DIF_OK(
      dif_usbdev_data_toggle_in_write(&usbdev, all_endpoints, exp_in_toggles));

  // Check that they read as expected.
  check_toggles(exp_out_toggles, exp_in_toggles, logging);

  // Walk through each of the bits within each register, setting and resetting
  // each bit individually.
  for (uint8_t ep = 0u; ep < USBDEV_NUM_ENDPOINTS; ++ep) {
    uint16_t ep_mask = (uint16_t)(1u << ep);

    exp_out_toggles |= ep_mask;
    exp_in_toggles |= ep_mask;
    CHECK_DIF_OK(dif_usbdev_data_toggle_out_write(&usbdev, ep_mask, ep_mask));
    CHECK_DIF_OK(dif_usbdev_data_toggle_in_write(&usbdev, ep_mask, ep_mask));

    check_toggles(exp_out_toggles, exp_in_toggles, logging);

    exp_out_toggles &= ~ep_mask;
    exp_in_toggles &= ~ep_mask;
    CHECK_DIF_OK(dif_usbdev_data_toggle_out_write(&usbdev, ep_mask, 0u));
    CHECK_DIF_OK(dif_usbdev_data_toggle_in_write(&usbdev, ep_mask, 0u));

    check_toggles(exp_out_toggles, exp_in_toggles, logging);
  }

  // Tidy up by disconnecting from the USB.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleDisabled));

  return true;
}
