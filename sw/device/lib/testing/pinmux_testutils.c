// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "dt/dt_pinmux.h"
#include "dt/dt_uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"

static const dt_gpio_t kGpioDt = kDtGpio;
static const dt_uart_t kUart0Dt = kDtUart0;

#if defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
static const dt_pad_t kPadUart0Tx = kDtPadIoc4;
static const dt_pad_t kPadUart0Rx = kDtPadIoc3;
#define HAS_UART1
static const dt_uart_t kUart1Dt = kDtUart1;
static const dt_pad_t kPadUart1Tx = kDtPadIob5;
static const dt_pad_t kPadUart1Rx = kDtPadIob4;
static const dt_pad_t kPadStrap0 = kDtPadIoc0;
static const dt_pad_t kPadStrap1 = kDtPadIoc1;
static const dt_pad_t kPadStrap2 = kDtPadIoc2;

#elif defined(OPENTITAN_IS_DARJEELING)
static const dt_pad_t kPadUart0Tx = kDtPadUart0Tx;
static const dt_pad_t kPadUart0Rx = kDtPadUart0Rx;
/* No UART1 */
static const dt_pad_t kPadStrap0 = kDtPadGpioGpio22;
static const dt_pad_t kPadStrap1 = kDtPadGpioGpio23;
static const dt_pad_t kPadStrap2 = kDtPadGpioGpio24;

#else /* OPENTITAN_IS_* */
#error Unsupported top
#endif /* OPENTITAN_IS_* */

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  // Set up SW straps on IOC0-IOC2, for GPIOs 22-24
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio22),
      kDtPeriphIoDirIn, kPadStrap0));
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio23),
      kDtPeriphIoDirIn, kPadStrap1));
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_gpio_periph_io(kGpioDt, kDtGpioPeriphIoGpio24),
      kDtPeriphIoDirIn, kPadStrap2));

  // Configure UART0 RX input.
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_uart_periph_io(kUart0Dt, kDtUartPeriphIoRx), kDtPeriphIoDirIn,
      kPadUart0Rx));
  // Configure UART0 TX output.
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_uart_periph_io(kUart0Dt, kDtUartPeriphIoTx), kDtPeriphIoDirOut,
      kPadUart0Tx));

#ifdef OPENTITAN_IS_EARLGREY
  // Enable pull-ups on UART0 RX
  // Pull-ups are available only on certain platforms.
  if (kDeviceType == kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0,
        .drive_strength = 0,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp};

    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs_dt(pinmux, kPadUart0Rx, in_attr, &out_attr));
  };
#endif

#ifdef HAS_UART1
  // Configure UART1 RX input.
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_uart_periph_io(kUart1Dt, kDtUartPeriphIoRx), kDtPeriphIoDirIn,
      kPadUart1Rx));
  // Configure UART1 TX output.
  CHECK_STATUS_OK(pinmux_testutils_connect(
      pinmux, dt_uart_periph_io(kUart1Dt, kDtUartPeriphIoTx), kDtPeriphIoDirOut,
      kPadUart1Tx));
#endif /* HAS_UART1 */

#ifdef OPENTITAN_IS_EARLGREY
  // Configure a higher drive strength for the USB_P and USB_N pads because
  // the pad drivers must be capable of overpowering the 'pull' signal
  // strength of the internal pull ups in the differential receiver.
  //
  // 'pull' strength is required because at the host end of the USB, there
  // are 'weak' pull downs, allowing it to detect device presence when it
  // applies its pull up.
  //    strong PAD driver > internal pull up > weak pull down at host
  //
  // Normally the pull up on USB_P will be asserted, but we may be employing
  // 'pin flipping' and instead choose to apply the _N pull up.
  if (kDeviceType == kDeviceSimDV) {
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 0, .drive_strength = 1, .flags = 0};

    CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, kDtPadUsbdevUsbDp,
                                               in_attr, &out_attr));
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, kDtPadUsbdevUsbDn,
                                               in_attr, &out_attr));
  }

  // Configure USBDEV SENSE outputs to be high-Z (IOC7)
  CHECK_DIF_OK(dif_pinmux_mio_select_output(pinmux, kDtPadIoc7,
                                            kDtPeriphIoConstantHighZ));
#endif /* OPENTITAN_IS_EARLGREY* */
}

status_t pinmux_testutils_connect(const dif_pinmux_t *pinmux,
                                  dt_periph_io_t periph_io,
                                  dt_periph_io_dir_t dir, dt_pad_t pad) {
  switch (dt_periph_io_type(periph_io)) {
    case kDtPeriphIoTypeMio:
      if (dt_pad_type(pad) != kDtPadTypeMio) {
        return INVALID_ARGUMENT();
      }
      // Configure input.
      if (dir == kDtPeriphIoDirIn || dir == kDtPeriphIoDirInout) {
        TRY(dif_pinmux_mio_select_input(pinmux, periph_io, pad));
      }
      // Configure output as requested...
      if (dir == kDtPeriphIoDirOut || dir == kDtPeriphIoDirInout) {
        TRY(dif_pinmux_mio_select_output(pinmux, pad, periph_io));
      }
      // ... or as high-Z.
      else if (dt_periph_io_dir(periph_io) == kDtPeriphIoDirInout) {
        TRY(dif_pinmux_mio_select_output(pinmux, pad,
                                         kDtPeriphIoConstantHighZ));
      }
      return OK_STATUS();
    case kDtPeriphIoTypeDio:
      // Nothing to do but to check that they are actually connected together.
      if (dt_pad_type(pad) != kDtPadTypeDio ||
          dt_periph_io_dio_pad(periph_io) != pad) {
        return INVALID_ARGUMENT();
      }
      // Make sure that the directions are compatible.
      dt_periph_io_dir_t io_dir = dt_periph_io_dir(periph_io);
      if ((io_dir == kDtPeriphIoDirIn || io_dir == kDtPeriphIoDirOut) &&
          dir != io_dir) {
        return INVALID_ARGUMENT();
      }
      return OK_STATUS();
    default:
      return INVALID_ARGUMENT();
  }
}

// Mapping of Chip IOs to the GPIO peripheral.
//
// Depending on the simulation platform, there may be a limitation to how chip
// IOs are allocated to the GPIO peripheral, even for testing. The DV testbench
// does not have this limitation, and is able to allocate as many chip IOs as
// the number of GPIOs supported by the peripheral. At this time, these pin
// assignments matches DV (see `hw/top_earlgrey/dv/env/chip_if.sv`).
//
// The pinout spreadsheet allocates fewer pins to GPIOs than what the GPIO IP
// supports. This oversubscription is intentional to maximize testing.
#if defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
const dt_pad_t kPinmuxTestutilsGpioPads[kDifGpioNumPins] = {
    kDtPadIoa0,  kDtPadIoa1, kDtPadIoa2,  kDtPadIoa3,  kDtPadIoa4,
    kDtPadIoa5,  kDtPadIoa6, kDtPadIoa7,  kDtPadIoa8,  kDtPadIob6,
    kDtPadIob7,  kDtPadIob8, kDtPadIob9,  kDtPadIob10, kDtPadIob11,
    kDtPadIob12, kDtPadIoc9, kDtPadIoc10, kDtPadIoc11, kDtPadIoc12,
    kDtPadIor0,  kDtPadIor1, kDtPadIor2,  kDtPadIor3,  kDtPadIor4,
    kDtPadIor5,  kDtPadIor6, kDtPadIor7,  kDtPadIor10, kDtPadIor11,
    kDtPadIor12, kDtPadIor13};
#elif defined(OPENTITAN_IS_DARJEELING)
const dt_pad_t kPinmuxTestutilsGpioPads[kDifGpioNumPins] = {
    kDtPadGpioGpio0,  kDtPadGpioGpio1,  kDtPadGpioGpio2,  kDtPadGpioGpio3,
    kDtPadGpioGpio4,  kDtPadGpioGpio5,  kDtPadGpioGpio6,  kDtPadGpioGpio7,
    kDtPadGpioGpio8,  kDtPadGpioGpio9,  kDtPadGpioGpio10, kDtPadGpioGpio11,
    kDtPadGpioGpio12, kDtPadGpioGpio13, kDtPadGpioGpio14, kDtPadGpioGpio15,
    kDtPadGpioGpio16, kDtPadGpioGpio17, kDtPadGpioGpio18, kDtPadGpioGpio19,
    kDtPadGpioGpio20, kDtPadGpioGpio21, kDtPadGpioGpio22, kDtPadGpioGpio23,
    kDtPadGpioGpio24, kDtPadGpioGpio25, kDtPadGpioGpio26, kDtPadGpioGpio27,
    kDtPadGpioGpio28, kDtPadGpioGpio29, kDtPadGpioGpio30, kDtPadGpioGpio31,
};
#else /* OPENTITAN_IS_* */
#error Unsupported top
#endif /* OPENTITAN_IS_* */

uint32_t pinmux_testutils_get_testable_gpios_mask(void) {
  switch (kDeviceType) {
    case kDeviceSimDV:
    case kDeviceSimVerilator:
      // All GPIOs are testable in DV.
      return 0xffffffff;
    case kDeviceFpgaCw310:
      // Only IOR6, IOR7, and IOR10 to IOR13 are available for use as GPIOs.
      return 0xfc000000;
    case kDeviceSilicon:
      // IOA3/6, IOB6, IOC9-12, IOR5-7 and IOR10-13.
      return 0xfe0f0248;
    default:
      CHECK(false);
      return 0;
  }
}

uint32_t pinmux_testutils_read_strap_pin(dif_pinmux_t *pinmux, dif_gpio_t *gpio,
                                         dif_gpio_pin_t io, dt_pad_t pad) {
  // Turn off the pull enable on the pad and read the IO.
  dif_pinmux_pad_attr_t attr = {.flags = 0};
  dif_pinmux_pad_attr_t attr_out;
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, pad, attr, &attr_out));
  // Let the change propagate.
  busy_spin_micros(100);
  bool state;
  // The value read is unmodified by the internal pull resistors and represents
  // the upper bit of the 4 possible states [Strong0, Weak0, Weak1,
  // Strong1].
  CHECK_DIF_OK(dif_gpio_read(gpio, io, &state));
  uint32_t result = state ? 2 : 0;

  // Based on the previous read, enable the opposite pull resistor.  If the
  // external signal is weak, the internal pull resistor will win; if the
  // external signal is strong, the external value will win.
  attr.flags = kDifPinmuxPadAttrPullResistorEnable |
               (state ? 0 : kDifPinmuxPadAttrPullResistorUp);
  CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, pad, attr, &attr_out));
  // Let the change propagate.
  busy_spin_micros(100);
  // Combine the result of the contest between the external signal in internal
  // pull resistors.  This represents the lower bit of the 4 possible states.
  CHECK_DIF_OK(dif_gpio_read(gpio, io, &state));
  result += state ? 1 : 0;
  return result;
}

uint32_t pinmux_testutils_read_straps(dif_pinmux_t *pinmux, dif_gpio_t *gpio) {
  uint32_t strap = 0;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 22, kPadStrap0);
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 23, kPadStrap1) << 2;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, 24, kPadStrap2) << 4;
  return strap;
}

void pinmux_testutils_configure_pads(const dif_pinmux_t *pinmux,
                                     const pinmux_pad_attributes_t *attrs,
                                     size_t num_attrs) {
  for (size_t i = 0; i < num_attrs; ++i) {
    dif_pinmux_pad_attr_t desired_attr, actual_attr;
    CHECK_DIF_OK(
        dif_pinmux_pad_get_attrs_dt(pinmux, attrs[i].pad, &desired_attr));
    desired_attr.flags = attrs[i].flags;
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(pinmux, attrs[i].pad,
                                               desired_attr, &actual_attr));
  }
}
