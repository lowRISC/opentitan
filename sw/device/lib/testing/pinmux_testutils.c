// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/pinmux_testutils.h"

#include "hw/top/dt/pinmux.h"
#include "hw/top/dt/uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"

static const dt_uart_t kUart0Dt = kDtUart0;

#if defined(OPENTITAN_IS_EARLGREY)
// The SW straps can only be read by gpio1 IOs 2-4 due to the sparse pinmux.
static const dt_gpio_t kStrapGpioDt = kDtGpio1;
static const dif_gpio_pin_t kStrapGpioPin0 = 2;
#else
static const dt_gpio_t kStrapGpioDt = kDtGpio0;
static const dif_gpio_pin_t kStrapGpioPin0 = 22;
#endif

#if defined(OPENTITAN_IS_EARLGREY) || defined(OPENTITAN_IS_ENGLISHBREAKFAST)
static const dt_pad_t kPadUart0Tx = kDtPadIoc4;
static const dt_pad_t kPadUart0Rx = kDtPadIoc3;
static const dt_pad_t kPadStrap0 = kDtPadIoc0;
static const dt_pad_t kPadStrap1 = kDtPadIoc1;
static const dt_pad_t kPadStrap2 = kDtPadIoc2;

#elif defined(OPENTITAN_IS_DARJEELING)
static const dt_pad_t kPadUart0Tx = kDtPadUart0Tx;
static const dt_pad_t kPadUart0Rx = kDtPadUart0Rx;
static const dt_pad_t kPadStrap0 = kDtPadGpio0Gpio22;
static const dt_pad_t kPadStrap1 = kDtPadGpio0Gpio23;
static const dt_pad_t kPadStrap2 = kDtPadGpio0Gpio24;

#else /* OPENTITAN_IS_* */
#error Unsupported top
#endif /* OPENTITAN_IS_* */

void pinmux_testutils_init(dif_pinmux_t *pinmux) {
  // Set up the SW straps.
  const dt_pad_t strap_pads[] = {kPadStrap0, kPadStrap1, kPadStrap2};
  for (size_t i = 0; i < ARRAYSIZE(strap_pads); ++i) {
    dt_gpio_periph_io_t io =
        (dt_gpio_periph_io_t)(kDtGpioPeriphIoGpio0 + kStrapGpioPin0 + i);
    CHECK_STATUS_OK(
        pinmux_testutils_connect(pinmux, dt_gpio_periph_io(kStrapGpioDt, io),
                                 kDtPeriphIoDirIn, strap_pads[i]));
  }

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
#if defined(OPENTITAN_IS_EARLGREY)
// Each GPIO pin can only reach one pad. The table lists all 32 pins of
// each instance: gpio1 pins 29-31 repeat the pads of pins 25-27 (IOR10-IOR12)
// and are left out of the testable masks below to avoid contention.
const dt_pad_t kPinmuxTestutilsGpioPads[kDtGpioCount][kDifGpioNumPins] = {
    {
        kDtPadSpiHostD0,  kDtPadSpiHostD1,  kDtPadSpiHostD2, kDtPadSpiHostD3,
        kDtPadSpiHostClk, kDtPadSpiHostCsL, kDtPadSpiDevD0,  kDtPadSpiDevD1,
        kDtPadSpiDevD2,   kDtPadSpiDevD3,   kDtPadSpiDevClk, kDtPadSpiDevCsL,
        kDtPadIoa0,       kDtPadIoa1,       kDtPadIoa2,      kDtPadIoa3,
        kDtPadIoa4,       kDtPadIoa5,       kDtPadIoa6,      kDtPadIoa7,
        kDtPadIoa8,       kDtPadIob0,       kDtPadIob1,      kDtPadIob2,
        kDtPadIob3,       kDtPadIob4,       kDtPadIob5,      kDtPadIob6,
        kDtPadIob7,       kDtPadIob8,       kDtPadIob9,      kDtPadIob10,
    },
    {
        kDtPadIob11, kDtPadIob12, kDtPadIoc0,  kDtPadIoc1,  kDtPadIoc2,
        kDtPadIoc3,  kDtPadIoc4,  kDtPadIoc5,  kDtPadIoc6,  kDtPadIoc7,
        kDtPadIoc8,  kDtPadIoc9,  kDtPadIoc10, kDtPadIoc11, kDtPadIoc12,
        kDtPadIor0,  kDtPadIor1,  kDtPadIor2,  kDtPadIor3,  kDtPadIor4,
        kDtPadIor5,  kDtPadIor6,  kDtPadIor7,  kDtPadIor8,  kDtPadIor9,
        kDtPadIor10, kDtPadIor11, kDtPadIor12, kDtPadIor13, kDtPadIor10,
        kDtPadIor11, kDtPadIor12,
    },
};
#elif defined(OPENTITAN_IS_ENGLISHBREAKFAST)
const dt_pad_t kPinmuxTestutilsGpioPads[kDtGpioCount][kDifGpioNumPins] = {
    {kDtPadIoa0,  kDtPadIoa1, kDtPadIoa2,  kDtPadIoa3,  kDtPadIoa4,
     kDtPadIoa5,  kDtPadIoa6, kDtPadIoa7,  kDtPadIoa8,  kDtPadIob6,
     kDtPadIob7,  kDtPadIob8, kDtPadIob9,  kDtPadIob10, kDtPadIob11,
     kDtPadIob12, kDtPadIoc9, kDtPadIoc10, kDtPadIoc11, kDtPadIoc12,
     kDtPadIor0,  kDtPadIor1, kDtPadIor2,  kDtPadIor3,  kDtPadIor4,
     kDtPadIor5,  kDtPadIor6, kDtPadIor7,  kDtPadIor10, kDtPadIor11,
     kDtPadIor12, kDtPadIor13}};
#elif defined(OPENTITAN_IS_DARJEELING)
const dt_pad_t kPinmuxTestutilsGpioPads[kDtGpioCount][kDifGpioNumPins] = {{
    kDtPadGpio0Gpio0,  kDtPadGpio0Gpio1,  kDtPadGpio0Gpio2,  kDtPadGpio0Gpio3,
    kDtPadGpio0Gpio4,  kDtPadGpio0Gpio5,  kDtPadGpio0Gpio6,  kDtPadGpio0Gpio7,
    kDtPadGpio0Gpio8,  kDtPadGpio0Gpio9,  kDtPadGpio0Gpio10, kDtPadGpio0Gpio11,
    kDtPadGpio0Gpio12, kDtPadGpio0Gpio13, kDtPadGpio0Gpio14, kDtPadGpio0Gpio15,
    kDtPadGpio0Gpio16, kDtPadGpio0Gpio17, kDtPadGpio0Gpio18, kDtPadGpio0Gpio19,
    kDtPadGpio0Gpio20, kDtPadGpio0Gpio21, kDtPadGpio0Gpio22, kDtPadGpio0Gpio23,
    kDtPadGpio0Gpio24, kDtPadGpio0Gpio25, kDtPadGpio0Gpio26, kDtPadGpio0Gpio27,
    kDtPadGpio0Gpio28, kDtPadGpio0Gpio29, kDtPadGpio0Gpio30, kDtPadGpio0Gpio31,
}};
#else /* OPENTITAN_IS_* */
#error Unsupported top
#endif /* OPENTITAN_IS_* */

// Testable GPIO pins per device type and GPIO instance. Devices without an
// entry are not supported.
#if defined(OPENTITAN_IS_EARLGREY)
// Each entry is {gpio0 mask, gpio1 mask}.
static const uint32_t kTestableGpiosMask[][kDtGpioCount] = {
    // DV can test each pin except the TAP straps on IOC5 and IOC8. In
    // DFT-enabled LC states these are sampled continuously, so toggling them
    // would switch the selected TAP. Thus we have to ignore the GPIOs of
    // these pads. These GPIOs are on gpio1 pin 7 and 10.
    [kDeviceSimDV] = {0xffffffff, 0x1ffffb7f},
    // gpio0: IOA0-8, IOB6-10
    // gpio1: IOB11-12, IOC9-12, IOR0-7, IOR10-13.
    [kDeviceSimVerilator] = {0xf81ff000, 0x1e7ff803},
    // Only IOR6, IOR7, and IOR10 to IOR13 are available for use as GPIOs.
    // On the CW340 IOR6 faces the HyperDebug UART4 RX input.
    [kDeviceFpgaCw310] = {0, 0x1e600000},
    [kDeviceFpgaCw340] = {0, 0x1e600000},
    // IOA3/6, IOB6, IOC9-12, IOR5-7 and IOR10-13.
    [kDeviceSilicon] = {0x08048000, 0x1e707800},
};
#else
// Each entry is {gpio0 mask}.
static const uint32_t kTestableGpiosMask[][kDtGpioCount] = {
    // All GPIOs are testable in DV.
    [kDeviceSimDV] = {0xffffffff},
    [kDeviceSimVerilator] = {0xffffffff},
    // Only IOR6, IOR7, and IOR10 to IOR13 are available for use as GPIOs.
    [kDeviceFpgaCw310] = {0xfc000000},
    [kDeviceFpgaCw340] = {0xfc000000},
    // IOA3/6, IOB6, IOC9-12, IOR5-7 and IOR10-13.
    [kDeviceSilicon] = {0xfe0f0248},
};
#endif

uint32_t pinmux_testutils_get_testable_gpios_mask(dt_gpio_t gpio) {
  CHECK((size_t)kDeviceType < ARRAYSIZE(kTestableGpiosMask));
  CHECK(gpio < kDtGpioCount);
  const uint32_t *masks = kTestableGpiosMask[kDeviceType];
  // Catch errors in the table definition: a device without an entry gets an
  // all-zero row.
  bool supported = false;
  for (size_t i = 0; i < kDtGpioCount; ++i) {
    supported |= masks[i] != 0;
  }
  CHECK(supported);
  return masks[gpio];
}

#if defined(OPENTITAN_IS_EARLGREY)
// A list specifying which pads are driven by other devices on the CW340 and
// thus should not be driven by GPIO tests. The opposite of this table is in
// sw/host/tests/chip/gpio/src/fpga_pads.rs.
static const dt_pad_t kCw340BoardDrivenPads[] = {
    // HyperDebug JTAG.
    kDtPadIoa0,
    kDtPadIoa4,
    kDtPadIoa5,
    kDtPadIoa6,
    // HyperDebug I2C1, I2C3 and I2C2.
    kDtPadIoa7,
    kDtPadIoa8,
    kDtPadIob9,
    kDtPadIob10,
    kDtPadIob11,
    kDtPadIob12,
    // HyperDebug SPI2, from its boot and in the reinit of every
    // `transport init`.
    kDtPadIob0,
    kDtPadIob1,
    kDtPadIob3,
    // HyperDebug UART3 TX while the UART2_HOST_TX strapping is applied.
    kDtPadIob4,
    // I3C test board UART TX.
    kDtPadIob7,
    // SW straps and TAP straps.
    kDtPadIoc0,
    kDtPadIoc1,
    kDtPadIoc2,
    kDtPadIoc5,
    kDtPadIoc8,
    // HyperDebug UART2 TX, the console input.
    kDtPadIoc3,
    // HyperDebug PWM / external clock.
    kDtPadIoc6,
    // USB VBUS detect divider on the CW341.
    kDtPadIoc7,
    // HyperDebug UART5 TX and UART4 TX.
    kDtPadIor3,
    kDtPadIor5,
    // HyperDebug QSPI.
    kDtPadSpiDevD0,
    kDtPadSpiDevD1,
    kDtPadSpiDevD2,
    kDtPadSpiDevD3,
    kDtPadSpiDevClk,
    kDtPadSpiDevCsL,
};
#endif

bool pinmux_testutils_is_board_driven_pad(dt_pad_t pad) {
#if defined(OPENTITAN_IS_EARLGREY)
  if (kDeviceType == kDeviceFpgaCw340) {
    for (size_t i = 0; i < ARRAYSIZE(kCw340BoardDrivenPads); ++i) {
      if (kCw340BoardDrivenPads[i] == pad) {
        return true;
      }
    }
  }
#else
  (void)pad;
#endif
  return false;
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
  strap |=
      pinmux_testutils_read_strap_pin(pinmux, gpio, kStrapGpioPin0, kPadStrap0);
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, kStrapGpioPin0 + 1,
                                           kPadStrap1)
           << 2;
  strap |= pinmux_testutils_read_strap_pin(pinmux, gpio, kStrapGpioPin0 + 2,
                                           kPadStrap2)
           << 4;
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
