// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USB device packet transmission test
//
// This test enables the `packet transmission` test mode within the USB
// device. That test mode has been added to simplify the electrical
// compliance testing of the USB device by ensuring that the USB device
// is transmitting continuously and that there is no other bus traffic
// on the USB link.
//
// The content of the test packet is chosen to resemble that specified for
// High Speed devices, although it is of course being transmitted using
// Full Speed signaling.
//
// The test code does not receive any communication from the USB host
// controller but still requires a VBUS connection because otherwise the
// link will sit in reset.
//
// NOTE: This functionality is not present in Earl Grey but has been added
// for devices including later revisions of the USBDEV IP.

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

/**
 * USB device handle
 */
static dif_usbdev_t usbdev;
static dif_usbdev_buffer_pool_t buffer_pool;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

/**
 * The test packet to be transmitted; this is the data field within a single
 * DATA0 packet, so it gets prefixed with SYNC and DATA0 PID, and then the
 * CRC16 is appended.
 *
 * The content is constructed as per section 7.1.20 Test Mode Support,
 * prior to the bitstuffing.
 */
static const uint8_t test_packet[] = {
    0x00u, 0x00u, 0x00u, 0x00u, 0x00u, 0x00u, 0x00u, 0x00u, 0x00u, 0xaau, 0xaau,
    0xaau, 0xaau, 0xaau, 0xaau, 0xaau, 0xaau, 0xeeu, 0xeeu, 0xeeu, 0xeeu, 0xeeu,
    0xeeu, 0xeeu, 0xeeu, 0xfeu, 0xffu, 0xffu, 0xffu, 0xffu, 0xffu, 0xffu, 0xffu,
    0xffu, 0xffu, 0xffu, 0xffu, 0x7fu, 0xbfu, 0xdfu, 0xefu, 0xf7u, 0xfbu, 0xfdu,
    0xfcu, 0x7eu, 0xbfu, 0xdfu, 0xefu, 0xf7u, 0xfbu, 0xfdu, 0x7eu};
static_assert(sizeof(test_packet) == 0x35u, "Incorrect test packet length");

// Wait with optional timeout until the VBUS/SENSE signal is in the expected
// state. A timeout of UINT32_MAX means 'wait indefinitely.'
static status_t vbus_wait(bool expected, uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Read the current state of VBUS.
    bool vbus;
    TRY(dif_usbdev_status_get_sense(&usbdev, &vbus));
    if (vbus == expected) {
      return OK_STATUS();
    }
  } while (timeout_micros == UINT32_MAX || !ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
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

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  uint32_t timeout_micros = 1000u;
  uint32_t delay_micros = 1u;
  bool prompt = false;

  switch (kDeviceType) {
    // In simulation the DPI model connects VBUS shortly after reset.
    case kDeviceSimDV:
    case kDeviceSimVerilator:
      timeout_micros = 1000u;
      break;
    default:
      // FPGA platforms where user intervention may be required.
      timeout_micros = 30 * 1000 * 1000u;
      // A short delay here permits the activity of the host controller to be
      // observed (eg. dmesg -w on a Linux host).
      delay_micros = 2 * 1000 * 1000u;
      // Report instructions/progress to user, when driven manually.
      prompt = true;

      LOG_INFO("Running USBDEV_TX_PKT test");
      break;
  }

  // Ensure that the VBUS/SENSE signal is routed through to the usbdev
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // Set up access to the device and ensure that we can allocate a packet
  // buffer as required.
  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));

  dif_usbdev_config_t config = {
      .have_differential_receiver = kDifToggleEnabled,
      .use_tx_d_se0 = kDifToggleDisabled,
      .single_bit_eop = kDifToggleDisabled,
      .pin_flip = kDifToggleDisabled,
      .clock_sync_signals = kDifToggleEnabled,
  };

  CHECK_DIF_OK(dif_usbdev_configure(&usbdev, &buffer_pool, config));

  // Check for VBUS present/risen.
  CHECK_STATUS_OK(vbus_wait(true, timeout_micros));

  // Delay a little, mostly to slow things on user-driven FPGA for
  // observation.
  CHECK_STATUS_OK(delay(prompt, delay_micros));
  // prompt = true;
  if (prompt) {
    LOG_INFO("Connecting");
  }

  // We need to setup the appropriate configuration for Endpoint Zero,
  // but in this test we are concerned only with _sending_ a DATA packet,
  // so we must enable the IN endpoint.
  const uint8_t endpoint = 0u;
  dif_usbdev_endpoint_id_t ep_id = {0};
  ep_id.number = endpoint;
  ep_id.direction = USBDEV_ENDPOINT_DIR_IN;
  CHECK_DIF_OK(dif_usbdev_endpoint_enable(&usbdev, ep_id, kDifToggleEnabled));

  // Assert the D+ pull up, indicating the presence of a Full Speed device.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleEnabled));

  // Check the D+ line has risen.
  CHECK_STATUS_OK(line_wait(true, true, 1000u));

  // Program the test packet into a buffer.
  dif_usbdev_buffer_t buffer;
  CHECK_DIF_OK(dif_usbdev_buffer_request(&usbdev, &buffer_pool, &buffer));
  CHECK_DIF_OK(dif_usbdev_buffer_write(&usbdev, &buffer, test_packet,
                                       sizeof(test_packet), NULL));

  // Since there is a delay here on FPGA, we do not yet present the packet
  // for collection.
  if (prompt) {
    LOG_INFO("Starting packet transmission; will stop upon Bus Reset");
  }

  // Present the packet for transmission.
  CHECK_DIF_OK(dif_usbdev_send(&usbdev, endpoint, &buffer));
  // Enter test mode, immediately after presenting the packet.
  if (1) {
    // This TX Oscillator test mode has always existed in the USB device.
    CHECK_DIF_OK(dif_usbdev_set_test_mode(&usbdev, kDifUsbdevTestModeTxOsc));
  } else {
    // TX Packet test mode has been added only in more recent versions.
    CHECK_DIF_OK(dif_usbdev_set_test_mode(&usbdev, kDifUsbdevTestModeTxPacket));
  }

  // Wait until VBUS is disconnected; this should cause usbdev to exit the
  // test mode.
  CHECK_STATUS_OK(vbus_wait(false, UINT32_MAX));

  CHECK_DIF_OK(dif_usbdev_set_test_mode(&usbdev, kDifUsbdevTestModeNone));

  // Deassert the pull up, disconnect us from the bus.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleDisabled));

  // Dx line should drop in response.
  CHECK_STATUS_OK(line_wait(true, false, 1000u));

  return true;
}
