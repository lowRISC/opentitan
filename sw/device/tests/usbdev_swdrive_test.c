// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a simple test of the software-driven diagnostic input/output pins
// of the usbdev. It requires the SystemVerilog interface that forms part of the
// USB DPI model, so it works only in simulation.
//
// The normal usage of the input and output pins has no significance, and they
// are simply treated as GPIO. The test code runs them through all permutations
// to check the loopback connectivity provided when the DPI interface enters
// a special mode. This is achieved by a 'waggle dance' that disconnects the
// DPI model and enables loopback until the next reset.

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

/**
 * USBDEV handle
 */
static dif_usbdev_t usbdev;
static dif_usbdev_buffer_pool_t buffer_pool;

static const bool kVerbose = false;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK(kDeviceType == kDeviceSimVerilator,
        "This test is not expected to run on physical platforms; it requires "
        "the USB DPI model, so it works only in simulation.");

  LOG_INFO("Running USB SWDRIVE test");

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));

  // Ensure that the USB device has its default bus configuration
  dif_usbdev_config_t config = {
      .have_differential_receiver = dif_bool_to_toggle(false),
      .use_tx_d_se0 = dif_bool_to_toggle(false),
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = dif_bool_to_toggle(false),
      .clock_sync_signals = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_usbdev_configure(&usbdev, &buffer_pool, config));

  // Allow time for the DPI model to wake up
  busy_spin_micros(8u);

  // Desired drive state of output pins
  //
  // Note: this is the default 'Idle' state of the bus for a Full Speed device,
  //       so the DPI model will register our presence but not yet start talking
  dif_usbdev_phy_pins_drive_t drive = {
      // Single-ended output
      .data = true,
      .se0 = false,
      // Differential output
      .dp = true,
      .dn = false,
      // Configuration
      .diff_receiver_enable = false,
      .dp_pullup_en = true,
      .dn_pullup_en = false,
      .output_enable = true,
  };

  // Waggle the pull up enables through alternating states a few times to
  // activate the bypass logic in usbdpi.sv; this disconnects the DPI model
  // within the 'Reset Recovery' time so it doesn't try to communicate with the
  // device
  for (unsigned i = 0U; i < 16U; i++) {
    CHECK_DIF_OK(
        dif_usbdev_set_phy_pins_state(&usbdev, kDifToggleEnabled, drive));

    drive.dp_pullup_en = !drive.dp_pullup_en;
    drive.dn_pullup_en = !drive.dn_pullup_en;

    // A short delay makes the toggling of the pull up enables more apparent in
    // the simulation wavesforms, to differentiate it from normal USB behavior.
    busy_spin_micros(1u);
  }

  // Delay for a while to separate the 'waggle dance' from the loopback testing;
  // DPI model enters loopback mode
  busy_spin_micros(4u);

  // Sensed state of input pins
  dif_usbdev_phy_pins_sense_t sense;

  // Test the loopback path; requires DPI assistance because usbdev has
  // physically separate input and output buses.
  //
  // The interface to the DPI model (usbdpi.sv) loops back these 8 output pins,
  // which we drive through all permutations to check independence and
  // connectivity. The pins are not being used in their normal manner and the
  // DPI model has been disconnected.
  for (unsigned d = 0u; d < 0x100u; d++) {
    drive.dp = ((d & 1u) != 0u);
    drive.dn = ((d & 2u) != 0u);
    drive.data = ((d & 4u) != 0u);
    drive.se0 = ((d & 8u) != 0u);
    drive.output_enable = ((d & 0x10u) != 0u);
    drive.diff_receiver_enable = ((d & 0x20u) != 0u);
    drive.dp_pullup_en = ((d & 0x40u) != 0u);
    drive.dn_pullup_en = ((d & 0x80u) != 0u);

    CHECK_DIF_OK(
        dif_usbdev_set_phy_pins_state(&usbdev, kDifToggleEnabled, drive));

    // Read the state of the input pins; there's no need to await signal
    // propagation; it's faster than this software
    CHECK_DIF_OK(dif_usbdev_get_phy_pins_status(&usbdev, &sense));

    if (kVerbose) {
      uint32_t pins = (sense.vbus_sense ? 0x10000u : 0u) |
                      (sense.output_enable ? 0x1000u : 0u) |
                      (sense.tx_se0 ? 0x800u : 0u) |
                      (sense.tx_d ? 0x400u : 0u) | (sense.tx_dn ? 0x200u : 0u) |
                      (sense.tx_dp ? 0x100u : 0u) | (sense.rx_d ? 0x4u : 0u) |
                      (sense.rx_dn ? 0x2u : 0u) | (sense.rx_dp ? 0x1u : 0u);
      LOG_INFO("0x%x: 0x%x", d, pins);
    }

    // Check that the inputs we can monitor have been propagated from the
    // software override pins
    CHECK(sense.vbus_sense == drive.se0 && sense.rx_d == drive.data &&
          sense.rx_dp == drive.dp && sense.rx_dn == drive.dn);
  }

  // For the finale, enable the oscillator mode...which requires us to remove
  // the software override first
  CHECK_DIF_OK(
      dif_usbdev_set_phy_pins_state(&usbdev, kDifToggleDisabled, drive));
  CHECK_DIF_OK(dif_usbdev_set_osc_test_mode(&usbdev, kDifToggleEnabled));

  // Oscillator toggles DP/DN every bit interval (12Mbps), so we could sample a
  // few times with randomized delays to check that we see both states, but for
  // now just employ visual inspection.

  busy_spin_micros(0x40u);

  return true;
}
