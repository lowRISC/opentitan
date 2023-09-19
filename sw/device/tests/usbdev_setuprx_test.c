// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB SETUP RX test
//
// Test basic reception of SETUP token packet and associated DATA packet from
// the USB host.
//
// 1. Check for the presence of VBUS.
// 2. Assert the DP pull up, indicating the presence of a Full Speed device.
// 3. Check the DP line is high.
// 4. Wait until we receive an indication of SETUP packet reception or a timeout
//    occurs.
// 5. Check the properties of the SETUP packet but do NOT attempt a thorough
//    check of the packet content because it is not guaranteed what Control
//    Transfer will be performed first by the host.

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
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

// Wait with timeout for the receipt of packet from the host controller; this
// is expected to be the DATA packet indicating the start of a Control Transfer.
static status_t packet_wait(dif_usbdev_rx_packet_info_t *info,
                            dif_usbdev_buffer_t *buf, uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  do {
    // Attempt to collect a packet from the Rx FIFO.
    uint8_t depth;
    TRY(dif_usbdev_status_get_rx_fifo_depth(&usbdev, &depth));

    if (depth > 0u) {
      TRY(dif_usbdev_recv(&usbdev, info, buf));

      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

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

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK(kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSimVerilator ||
            kDeviceType == kDeviceFpgaCw310,
        "This test is not expected to run on platforms other than the "
        "Verilator/DV simulation or CW310 FPGA. It needs either the DPI model "
        "or a physical host, OS and drivers.");

  // In simulation the DPI model connects VBUS shortly after reset and
  // prolonged delays when asserting or deasserting pull ups are wasteful.
  uint32_t timeout_micros = 1000u;
  uint32_t delay_micros = 1u;
  bool prompt = false;

  if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) {
    // FPGA platforms where user intervention may be required.
    timeout_micros = 30 * 1000 * 1000u;
    // A short delay here permits the activity of the host controller to be
    // observed (eg. dmesg -w on a Linux host).
    delay_micros = 2 * 1000 * 1000u;
    // Report instructions/progress to user, when driven manually.
    prompt = true;
    LOG_INFO("Running USBDEV_SETUPRX test");
  }

  // Ensure that the VBUS/SENSE signal is routed through to the usbdev.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // Initialize and configure the usbdev with pin flipping set appropriately.
  CHECK_DIF_OK(
      dif_usbdev_init(mmio_region_from_addr(USBDEV_BASE_ADDR), &usbdev));
  CHECK_STATUS_OK(config_set(false));

  // Make some buffers available for received packets.
  CHECK_DIF_OK(dif_usbdev_fill_available_fifo(&usbdev, &buffer_pool));

  // Initially, if VBUS is low then prompt the user to establish the connection.
  if (prompt) {
    bool vbus;
    CHECK_DIF_OK(dif_usbdev_status_get_sense(&usbdev, &vbus));
    if (!vbus) {
      LOG_INFO("Connect or power up the USB");
    }
  }

  // Check for VBUS present/risen.
  CHECK_STATUS_OK(vbus_wait(true, timeout_micros));

  // Delay a little, mostly to slow things on user-driven FPGA for
  // observation.
  CHECK_STATUS_OK(delay(prompt, delay_micros));

  if (prompt) {
    LOG_INFO("Connecting");
  }

  // We need to setup the appropriate configuration for Endpoint Zero,
  // but in this test we are concerned only with OUT traffic from the host.
  const uint8_t endpoint = 0u;
  CHECK_DIF_OK(
      dif_usbdev_endpoint_setup_enable(&usbdev, endpoint, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_usbdev_endpoint_out_enable(&usbdev, endpoint, kDifToggleEnabled));
  CHECK_DIF_OK(dif_usbdev_endpoint_set_nak_out_enable(&usbdev, endpoint,
                                                      kDifToggleEnabled));
  dif_usbdev_endpoint_id_t ep_id = {0};
  ep_id.number = endpoint;
  ep_id.direction = USBDEV_ENDPOINT_DIR_OUT;
  CHECK_DIF_OK(dif_usbdev_endpoint_enable(&usbdev, ep_id, kDifToggleEnabled));

  // Assert the Dx pull up, indicating the presence of a Full Speed device.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleEnabled));

  // Check the Dx line has risen.
  CHECK_STATUS_OK(line_wait(true, true, 1000u));

  if (prompt) {
    LOG_INFO("Awaiting SETUP");
  }

  // Wait until we receive the first SETUP and DATA packets from the host.
  dif_usbdev_rx_packet_info_t info;
  dif_usbdev_buffer_t buffer;
  CHECK_STATUS_OK(packet_wait(&info, &buffer, timeout_micros));

  // Check the properties of the received packet; do not perform a complete
  // check of the packet contents because different hosts may initiate the
  // communication using different types of Control Transfer.
  CHECK(info.is_setup && !info.endpoint && info.length == 8u,
        "Received packet does not have the expected properties; expecting the "
        "start of a Control Transfer from the host.");

  uint8_t packet[USBDEV_MAX_PACKET_SIZE];
  size_t written;
  CHECK_DIF_OK(dif_usbdev_buffer_read(&usbdev, &buffer_pool, &buffer, packet,
                                      sizeof(packet), &written));
  CHECK(written == info.length, "Packet data is not of the expected length.");
  CHECK(packet[0] == 0x80u, "bmRequestType field not as expected");

  if (prompt) {
    // Display the packet contents just for additional confirmation.
    LOG_INFO("Setup stage:");

    base_hexdump_fmt_t fmt;
    fmt.bytes_per_word = 1u;
    fmt.words_per_line = 0x10u;
    fmt.alphabet = &kBaseHexdumpDefaultFmtAlphabet;
    base_hexdump_with(fmt, (char *)packet, written);

    LOG_INFO("Disconnecting");
  }

  // Deassert the pull up, disconnect us from the bus.
  CHECK_DIF_OK(dif_usbdev_interface_enable(&usbdev, kDifToggleDisabled));

  // Dx line should drop in response.
  CHECK_STATUS_OK(line_wait(true, false, 1000u));

  return true;
}
