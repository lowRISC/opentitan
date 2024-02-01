// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

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
    USB_CFG_DSCR_HEAD(USB_CFG_DSCR_LEN + USB_INTERFACE_DSCR_LEN, 1),
    // Single interface with no endpoint, just to make the host happy.
    VEND_INTERFACE_DSCR(0, 0, 0x50, 0),
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

static void init_peripherals(void) {
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  CHECK_STATUS_OK(usb_testutils_init(&usbdev, /*pinflip=*/false,
                                     /*en_diff_rcvr=*/true,
                                     /*tx_use_d_se0=*/false));
  CHECK_STATUS_OK(usb_testutils_controlep_init(
      &usbdev_control, &usbdev, 0, config_descriptors,
      sizeof(config_descriptors), NULL, 0));
}

// Enable/disable the AON Wake module, and wait with timeout until that has
// been confirmed.
static status_t aon_wait(dif_toggle_t enable) {
  // We must be sure that any alteration to the USBDEV pull up enables has
  // propagated through the CDC synchronizer and been sampled on the lower
  // frequency (200kHz) AON clock; allow 3 clock cycles.
  busy_spin_micros(15u);
  TRY(dif_usbdev_set_wake_enable(usbdev.dev, enable));
  // The AON Wake module operates on a 200kHz clock, so the clock period is
  // 5us; we have CDC between USBDEV and AON Wake, but it responds within a
  // couple of its clock cycles, so this is plenty.
  ibex_timeout_t timeout = ibex_timeout_init(20);
  do {
    dif_usbdev_wake_status_t status;
    TRY(dif_usbdev_get_wake_status(usbdev.dev, &status));
    // In the requested state yet?
    if (status.active == dif_toggle_to_bool(enable)) {
      return OK_STATUS();
    }
  } while (!ibex_timeout_check(&timeout));

  return DEADLINE_EXCEEDED();
}

static status_t wait_until_configured(uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  while (!ibex_timeout_check(&timeout)) {
    CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
    if (usbdev_control.device_state == kUsbTestutilsDeviceConfigured)
      return OK_STATUS();
  }
  return DEADLINE_EXCEEDED();
}

static status_t wait_until_suspended(uint32_t timeout_micros) {
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  while (usbdev_control.device_state == kUsbTestutilsDeviceConfigured &&
         !ibex_timeout_check(&timeout)) {
    CHECK_STATUS_OK(usb_testutils_poll(&usbdev));
    dif_usbdev_link_state_t link_state;
    CHECK_DIF_OK(dif_usbdev_status_get_link_state(usbdev.dev, &link_state));
    if (link_state == kDifUsbdevLinkStateSuspended) {
      return OK_STATUS();
    }
  }
  return DEADLINE_EXCEEDED();
}

static status_t wait_until_aon_bus_reset(uint32_t timeout_micros) {
  dif_usbdev_wake_status_t status;
  ibex_timeout_t timeout = ibex_timeout_init(timeout_micros);
  while (!ibex_timeout_check(&timeout)) {
    CHECK_DIF_OK(dif_usbdev_get_wake_status(usbdev.dev, &status));
    CHECK(status.active, "AON wake is not active?!");
    CHECK(!status.disconnected,
          "device was disconnected while waiting for reset");
    if (status.bus_reset)
      return OK_STATUS();
  }
  return DEADLINE_EXCEEDED();
}

bool test_main(void) {
  uint32_t timeout_micros = 30 * 1000 * 1000u;
  CHECK(kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator);

  init_peripherals();

  // Proceed only when the device has been configured.
  LOG_INFO("wait for host to configure device...");
  CHECK_STATUS_OK(wait_until_configured(timeout_micros));

  // Wait for the host to suspend the device.
  LOG_INFO("configured, waiting for suspend");
  CHECK_STATUS_OK(wait_until_suspended(timeout_micros));

  // Hand over control of the USB to the AON Wake module
  CHECK_STATUS_OK(aon_wait(kDifToggleEnabled));

  // Wait until AON reports a bus reset.
  LOG_INFO("suspended, waiting for reset");
  CHECK_STATUS_OK(wait_until_aon_bus_reset(timeout_micros));

  LOG_INFO("reset, take control back from aon");
  // Reclaim control of the USB by disabling the AON Wake module.
  CHECK_STATUS_OK(aon_wait(kDifToggleDisabled));

  CHECK_STATUS_OK(usb_testutils_fin(&usbdev));

  return true;
}
