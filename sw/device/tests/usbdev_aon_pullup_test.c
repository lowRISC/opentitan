// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB AON PULLUP test
//
// Test the driving of pull up resistor(s) on the USB, and check that the
// AON Wake module is able to maintain the state of the bus.
//
// 1.  Check for the presence of VBUS.
// 2.  Check the DP line is not in the desired state,
//     ie. initially it should be Low.
// 3.  Drive the DP line to the desired state.
// 4.  Check the DP line has changed as intended.
// 5.  Hand over control of the pull ups to the AON Wake module.
// 6.  Attempt to drive the DP line to the opposite state.
// 7.  Check that the DP line has not changed.
// 8.  Remove attempted change to the line state.
// 9.  Reclaim control of the pull ups from the AON Wake module.
// 10. Repeat steps 2 through 9 for driving DP low.
// [ Optionally
// 11. Enable pin flipping.
// 12. Repeat all of steps 2 through 10 for the DN line.
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

  return DEADLINE_EXCEEDED();
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

  return DEADLINE_EXCEEDED();
}

// Ensure that the specified USB data line remains in the expected state for
// (most of) the given time interval.
static status_t line_check(bool dp, bool expected, uint32_t interval_micros) {
  // The caveat here is that if we are connected to the host, we may
  // observe brief deviations from the expected state because the host
  // is trying to communicate with us.
  ibex_timeout_t timeout = ibex_timeout_init(interval_micros);
  uint32_t mismatched = 0u;
  uint32_t count = 0u;
  do {
    // Sense the current state of the pins.
    dif_usbdev_phy_pins_sense_t status;
    TRY(dif_usbdev_get_phy_pins_status(&usbdev, &status));

    mismatched += (dp ? status.rx_dp : status.rx_dn) ^ expected;
    ++count;
  } while (!ibex_timeout_check(&timeout));

  if ((mismatched << 3) > count) {
    // Line not in the expected state.
    return INTERNAL();
  }

  return OK_STATUS();
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

// Enable/disable the AON Wake module, and wait with timeout until that has
// been confirmed.
static status_t aon_wait(bool prompt, dif_toggle_t enable) {
  // We must be sure that any alteration to the USBDEV pull up enables has
  // propagated through the CDC synchronizer and been sampled on the lower
  // frequency (200kHz) AON clock; allow 3 clock cycles.
  TRY(delay(prompt, 15u));
  TRY(dif_usbdev_set_wake_enable(&usbdev, enable));
  // The AON Wake module operates on a 200kHz clock, so the clock period is
  // 5us; we have CDC between USBDEV and AON Wake, but it responds within a
  // couple of its clock cycles, so this is plenty.
  ibex_timeout_t timeout = ibex_timeout_init(20);
  do {
    dif_usbdev_wake_status_t status;
    TRY(dif_usbdev_get_wake_status(&usbdev, &status));
    // In the requested state yet?
    if (status.active == dif_toggle_to_bool(enable)) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // In simulation the DPI model connects VBUS shortly after reset and
  // prolonged delays when asserting or deasserting pull ups are wasteful.
  uint32_t timeout_micros = 1000u;
  uint32_t delay_micros = 1u;
  uint32_t hold_micros = 50u;
  bool can_flip = true;
  bool prompt = false;

  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    // FPGA platforms where user intervention may be required.
    timeout_micros = 30 * 1000 * 1000u;
    // A short delay here permits the activity of the host controller to be
    // observed (eg. dmesg -w on a Linux host).
    delay_micros = 2 * 1000 * 1000u;
    // Duration for which we should monitor the USB signal to check that it
    // doesn't change whilst AON Wake is holding it.
    hold_micros = 2 * 1000;
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

    // Check that the AON Wake module can maintain Dx the both Low
    // (disconnected) and High (connected) line states.
    bool desired = true;
    do {
      if (prompt) {
        LOG_INFO("Testing AON can hold %s %s", dp ? "DP" : "DN",
                 desired ? "High" : "Low");
      }
      // Check the Dx line is not in the desired state.
      CHECK_STATUS_OK(line_wait(dp, !desired, 1000u));

      // Delay a little, mostly to slow things on user-driven FPGA for
      // observation.
      CHECK_STATUS_OK(delay(prompt, delay_micros));

      // Assert the Dx pull up, indicating the presence of a Full Speed device.
      CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, desired));

      // Hand over control of the pull ups to the AON Wake module
      CHECK_STATUS_OK(aon_wait(prompt, kDifToggleEnabled));

      // Attempt to drive the Dx pull up into the opposite state
      if (prompt) {
        LOG_INFO(" - Attempting to drive %s %s", dp ? "DP" : "DN",
                 desired ? "Low" : "High");
      }
      CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, !desired));

      // Check that the AON Wake module has kept the pull ups in their original
      // state.
      CHECK_STATUS_OK(line_check(dp, desired, hold_micros));

      // Retract our efforts at changing Dx; this also should not change the
      // line state, just the intent of USBDEV.
      CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, desired));

      // Reclaim control of the pull ups by disabling the AON Wake module.
      CHECK_STATUS_OK(aon_wait(prompt, kDifToggleDisabled));

      // Check the Dx line is still in the desired state.
      CHECK_STATUS_OK(line_wait(dp, desired, 1000u));
      desired = !desired;
    } while (!desired);

    // Try again with the other line.
    dp = !dp;
  } while (can_flip && !dp);

  return true;
}
