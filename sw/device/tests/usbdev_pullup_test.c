// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB PULLUP test
//
// Test the driving of pull up resistor(s) that indicate the presence of usbdev
// on the USB, as well as its speed.
//
// 1. Check for the presence of VBUS.
// 2. Check the DP line is not high.
// 3. Assert the DP pull up, indicating the presence of a Full Speed device.
// 4. Check the DP line is high.
// 5. Deassert the DP pull up.
// [ Optionally
// 6. Enable pin flipping.
// 7. Assert the pull up again, now on the DN (Low Speed device to the host,
//    unless pins flipped externally).
// 8. Check the DN line is high.
// 9. Deassert the pull up.
// ]

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

/**
 * Are we expecting VBUS to be low at the start of the test, ie. no connection
 * to the physical host or the DPI model is inactive?
 */
static const bool kCheckLowFirst = false;

/**
 * USB device handle
 */
static dif_usbdev_t usbdev;
static dif_usbdev_buffer_pool_t buffer_pool;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

// Set the usbdev configuration according to whether or not pin flipping is
// desired.
static status_t config_set(bool pinflip) {
  dif_usbdev_config_t config = {
      .have_differential_receiver = kDifToggleEnabled,
      .use_tx_d_se0 = kDifToggleDisabled,
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = dif_bool_to_toggle(pinflip),
      .clock_sync_signals = kDifToggleEnabled,
  };

  TRY(dif_usbdev_configure(&usbdev, &buffer_pool, config));

  return OK_STATUS();
}

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

  return UNAVAILABLE();
}

// Wait with timeout for the specified USB data line to be in the expected
// state.
static status_t line_wait(bool dp, bool expected, uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Sense the current state of the pins.
    dif_usbdev_phy_pins_sense_t status;
    TRY(dif_usbdev_get_phy_pins_status(&usbdev, &status));

    if ((dp && status.rx_dp == expected) || (!dp && status.rx_dn == expected)) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return UNAVAILABLE();
}

// Delay for the specified number of microseconds, with user reporting for
// appropriate targets.
static status_t delay(bool prompt, uint32_t timeout_micros) {
  if (prompt) {
    LOG_INFO("Delaying...");
  }
  busy_spin_micros(timeout_micros);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // In simulation the DPI model connects VBUS shortly after reset and
  // prolonged delays when asserting or deasserting pull ups are wasteful.
  uint32_t timeout_micros = 1000u;
  uint32_t delay_micros = 1u;
  bool can_flip = true;
  bool prompt = false;

  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    // FPGA platforms where user intervention may be required.
    timeout_micros = 30 * 1000 * 1000u;
    // A short delay here permits the activity of the host controller to be
    // observed (eg. dmesg -w on a Linux host).
    delay_micros = 2 * 1000 * 1000u;
    // The CW310/340 board and their FPGA builds cannot raise the DN pull up
    // because the required resistor is not mounted by default.
    can_flip = false;
    // Report instructions/progress to user, when driven manually.
    prompt = true;
  }

  // Ensure that the VBUS/SENSE signal is routed through to the usbdev.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // DP line first (Full Speed device), and for some targets the only line that
  // has a pull up to be tested.
  bool dp = true;
  do {
    // Initialize and configure the usbdev with pin flipping set appropriately.
    CHECK_DIF_OK(
        dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));
    CHECK_STATUS_OK(config_set(!dp));

    // Initially the VBUS may be expected to be low; if so, ensure that this is
    // the case.
    if (kCheckLowFirst) {
      if (prompt) {
        bool vbus;
        CHECK_DIF_OK(dif_usbdev_status_get_sense(&usbdev, &vbus));
        if (vbus) {
          LOG_INFO("Disconnect or power down the USB");
        }
      }

      CHECK_STATUS_OK(vbus_wait(false, timeout_micros));

      if (prompt) {
        LOG_INFO("Connect or power up the USB");
      }
    }

    // Check for VBUS present/risen.
    CHECK_STATUS_OK(vbus_wait(true, timeout_micros));

    // Check the Dx line is low.
    CHECK_STATUS_OK(line_wait(dp, false, 1000u));

    // Delay a little, mostly to slow things on user-driven FPGA for
    // observation.
    CHECK_STATUS_OK(delay(prompt, delay_micros));

    // Assert the Dx pull up, indicating the presence of a Full Speed device.
    CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleEnabled));

    // Check the Dx line has risen.
    CHECK_STATUS_OK(line_wait(dp, true, 1000u));

    // Delay a while so that the activity of the host in detecting and
    // attempting to configure the device may be observed as additional
    // confirmation.
    CHECK_STATUS_OK(delay(prompt, delay_micros));

    // Deassert the pull up, disconnect us from the bus.
    CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleDisabled));

    // Dx line should drop in response.
    CHECK_STATUS_OK(line_wait(dp, false, 1000u));

    // Try again with the other line.
    dp = !dp;
  } while (can_flip && !dp);

  return true;
}
