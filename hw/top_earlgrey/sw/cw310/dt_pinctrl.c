// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/devicetables/dt.h"
#include "sw/device/lib/devicetables/dt_i2c.h"
#include "sw/device/lib/devicetables/dt_pwm.h"
#include "sw/device/lib/devicetables/dt_spi_device.h"
#include "sw/device/lib/devicetables/dt_spi_host.h"
#include "sw/device/lib/devicetables/dt_sysrst_ctrl.h"
#include "sw/device/lib/devicetables/dt_uart.h"
#include "sw/device/lib/devicetables/dt_usbdev.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static bool pinctrl_ok[kDtDeviceIdCount] = {
    [kDtDeviceIdUart0] = true,    [kDtDeviceIdUart1] = true,
    [kDtDeviceIdUart2] = true,    [kDtDeviceIdUart3] = true,
    [kDtDeviceIdGpio] = true,     [kDtDeviceIdSpiDevice] = true,
    [kDtDeviceIdI2c0] = true,     [kDtDeviceIdI2c1] = true,
    [kDtDeviceIdI2c2] = true,     [kDtDeviceIdPattgen] = true,
    [kDtDeviceIdSpiHost0] = true, [kDtDeviceIdSpiHost1] = true,
    [kDtDeviceIdUsbdev] = true,   [kDtDeviceIdSysrstCtrlAon] = true,
    [kDtDeviceIdPwmAon] = true,
};

bool dt_device_pinctrl_is_ok(dt_device_t dev) {
  if (dev < kDtDeviceIdCount) {
    return pinctrl_ok[dev];
  }
  return false;
}

// Probably want enums that define where in the table a given device begins

// Might need to look up by specific signal, since sometimes, only some of the
// pins are connected. For example, UART might only connect one of the two
// directions. If the user supplies the device and pin, we can construct a flat
// table pretty easily...
static const dt_pinctrl_cfg_t
    padmux_uart[kDtDeviceCountUart][kDtUartPinctrlOutputCount] = {
        [0] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxMioOutIoc3,
                    kTopEarlgreyPinmuxOutselConstantHighZ),
                [kDtUartPinctrlOutputTx] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc4,
                                              kTopEarlgreyPinmuxOutselUart0Tx),
            },
        [1] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxMioOutIob4,
                    kTopEarlgreyPinmuxOutselConstantHighZ),
                [kDtUartPinctrlOutputTx] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIob5,
                                              kTopEarlgreyPinmuxOutselUart1Tx),
            },
        [2] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxMioOutIoa0,
                    kTopEarlgreyPinmuxOutselConstantHighZ),
                [kDtUartPinctrlOutputTx] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoa1,
                                              kTopEarlgreyPinmuxOutselUart2Tx),
            },
        [3] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxMioOutIoa4,
                    kTopEarlgreyPinmuxOutselConstantHighZ),
                [kDtUartPinctrlOutputTx] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoa5,
                                              kTopEarlgreyPinmuxOutselUart3Tx),
            },
};

static const dt_pinctrl_cfg_t
    periphmux_uart[kDtDeviceCountUart][kDtUartPinctrlInputCount] = {
        [0] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInUart0Rx,
                    kTopEarlgreyPinmuxInselIoc4),
            },
        [1] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInUart1Rx,
                    kTopEarlgreyPinmuxInselIob4),
            },
        [2] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInUart2Rx,
                    kTopEarlgreyPinmuxInselIoa0),
            },
        [3] =
            {
                [kDtUartPinctrlInputRx] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInUart3Rx,
                    kTopEarlgreyPinmuxInselIoa4),
            },
};

static const dt_pinctrl_cfg_t
    padmux_i2c[kDtDeviceCountI2c][kDtI2cPinctrlOutputCount] = {
        [0] =
            {
                [kDtI2cPinctrlInoutSda] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoa7,
                                              kTopEarlgreyPinmuxOutselI2c0Sda),
                [kDtI2cPinctrlInoutScl] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoa8,
                                              kTopEarlgreyPinmuxOutselI2c0Scl),
            },
        [1] =
            {
                [kDtI2cPinctrlInoutSda] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIob9,
                                              kTopEarlgreyPinmuxOutselI2c1Sda),
                [kDtI2cPinctrlInoutScl] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIob10,
                                              kTopEarlgreyPinmuxOutselI2c1Scl),
            },
        [2] =
            {
                [kDtI2cPinctrlInoutSda] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIob12,
                                              kTopEarlgreyPinmuxOutselI2c2Sda),
                [kDtI2cPinctrlInoutScl] =
                    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIob11,
                                              kTopEarlgreyPinmuxOutselI2c2Scl),
            },
};

static const dt_pinctrl_cfg_t
    periphmux_i2c[kDtDeviceCountI2c][kDtI2cPinctrlInputCount] = {
        [0] =
            {
                [kDtI2cPinctrlInoutSda] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c0Sda,
                    kTopEarlgreyPinmuxInselIoa7),
                [kDtI2cPinctrlInoutScl] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c0Scl,
                    kTopEarlgreyPinmuxInselIoa8),
            },
        [1] =
            {
                [kDtI2cPinctrlInoutSda] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c1Sda,
                    kTopEarlgreyPinmuxInselIob9),
                [kDtI2cPinctrlInoutScl] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c1Scl,
                    kTopEarlgreyPinmuxInselIob10),
            },
        [2] =
            {
                [kDtI2cPinctrlInoutSda] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c2Sda,
                    kTopEarlgreyPinmuxInselIob12),
                [kDtI2cPinctrlInoutScl] = dt_pinctrl_cfg_from_parts(
                    kTopEarlgreyPinmuxPeripheralInI2c2Scl,
                    kTopEarlgreyPinmuxInselIob11),
            },
};

static const dt_pinctrl_cfg_t padmux_spi_host1[kDtSpiHostPinctrlOutputCount] = {
    [kDtSpiHostPinctrlInoutSd0] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIob1, kTopEarlgreyPinmuxOutselSpiHost1Sd0),
    [kDtSpiHostPinctrlInoutSd1] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIob2, kTopEarlgreyPinmuxOutselSpiHost1Sd1),
    [kDtSpiHostPinctrlInoutSd2] = -1,
    [kDtSpiHostPinctrlInoutSd3] = -1,
    [kDtSpiHostPinctrlOutputCsb] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIob0, kTopEarlgreyPinmuxOutselSpiHost1Csb),
    [kDtSpiHostPinctrlOutputSck] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIob3, kTopEarlgreyPinmuxOutselSpiHost1Sck),
};

static const dt_pinctrl_cfg_t periphmux_spi_host1[kDtSpiHostPinctrlInputCount] =
    {
        [kDtSpiHostPinctrlInoutSd0] =
            dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,
                                      kTopEarlgreyPinmuxInselIob1),
        [kDtSpiHostPinctrlInoutSd1] =
            dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,
                                      kTopEarlgreyPinmuxInselIob2),
        [kDtSpiHostPinctrlInoutSd2] = -1,
        [kDtSpiHostPinctrlInoutSd3] = -1,
};

static const dt_pinctrl_cfg_t padmux_usbdev[kDtUsbdevPinctrlOutputCount] = {
    [kDtUsbdevPinctrlInputSense] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIoc7, kTopEarlgreyPinmuxOutselConstantHighZ),
    [kDtUsbdevPinctrlInoutUsbDp] = -1,
    [kDtUsbdevPinctrlInoutUsbDn] = -1,
};

static const dt_pinctrl_cfg_t periphmux_usbdev[kDtUsbdevPinctrlInputCount] = {
    [kDtUsbdevPinctrlInputSense] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxPeripheralInUsbdevSense, kTopEarlgreyPinmuxInselIoc7),
    [kDtUsbdevPinctrlInoutUsbDp] = -1,
    [kDtUsbdevPinctrlInoutUsbDn] = -1,
};

static const dt_pinctrl_cfg_t
    padmux_sysrst_ctrl[kDtSysrstCtrlPinctrlOutputCount] = {
        [kDtSysrstCtrlPinctrlInputAcPresent] =
            dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIor2,
                                      kTopEarlgreyPinmuxOutselConstantHighZ),
        [kDtSysrstCtrlPinctrlInputKey0In] = -1,
        [kDtSysrstCtrlPinctrlInputKey1In] = -1,
        [kDtSysrstCtrlPinctrlInputKey2In] = -1,
        [kDtSysrstCtrlPinctrlInputPwrbIn] = -1,
        [kDtSysrstCtrlPinctrlInputLidOpen] =
            dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIor11,
                                      kTopEarlgreyPinmuxOutselConstantHighZ),
        [kDtSysrstCtrlPinctrlInoutEcRstL] = -1,
        [kDtSysrstCtrlPinctrlInoutFlashWpL] = -1,
        [kDtSysrstCtrlPinctrlOutputBatDisable] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor12,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonBatDisable),
        [kDtSysrstCtrlPinctrlOutputKey0Out] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor6,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonKey0Out),
        [kDtSysrstCtrlPinctrlOutputKey1Out] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor7,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonKey1Out),
        [kDtSysrstCtrlPinctrlOutputKey2Out] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor13,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonKey2Out),
        [kDtSysrstCtrlPinctrlOutputPwrbOut] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor10,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonPwrbOut),
        [kDtSysrstCtrlPinctrlOutputZ3Wakeup] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxMioOutIor1,
            kTopEarlgreyPinmuxOutselSysrstCtrlAonZ3Wakeup),
};

static const dt_pinctrl_cfg_t
    periphmux_sysrst_ctrl[kDtSysrstCtrlPinctrlInputCount] = {
        [kDtSysrstCtrlPinctrlInputAcPresent] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent,
            kTopEarlgreyPinmuxInselIor2),
        [kDtSysrstCtrlPinctrlInputKey0In] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In,
            kTopEarlgreyPinmuxInselIor6),
        [kDtSysrstCtrlPinctrlInputKey1In] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In,
            kTopEarlgreyPinmuxInselIor7),
        [kDtSysrstCtrlPinctrlInputKey2In] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In,
            kTopEarlgreyPinmuxInselIor13),
        [kDtSysrstCtrlPinctrlInputPwrbIn] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn,
            kTopEarlgreyPinmuxInselIor10),
        [kDtSysrstCtrlPinctrlInputLidOpen] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen,
            kTopEarlgreyPinmuxInselIor11),
        [kDtSysrstCtrlPinctrlInoutEcRstL] = -1,
        [kDtSysrstCtrlPinctrlInoutFlashWpL] = -1,
};

static const dt_pinctrl_cfg_t padmux_pwm[kDtPwmPinctrlOutputCount] = {
    [kDtPwmPinctrlOutputPwm0] = dt_pinctrl_cfg_from_parts(
        kTopEarlgreyPinmuxMioOutIoc6, kTopEarlgreyPinmuxOutselPwmAonPwm0),
    [kDtPwmPinctrlOutputPwm1] = -1,
    [kDtPwmPinctrlOutputPwm2] = -1,
    [kDtPwmPinctrlOutputPwm3] = -1,
    [kDtPwmPinctrlOutputPwm4] = -1,
    [kDtPwmPinctrlOutputPwm5] = -1,
};

static const dt_pinctrl_cfg_t
    padmux_spi_device[kDtSpiDevicePinctrlOutputCount] = {
        [kDtSpiDevicePinctrlInputTpmCsb] =
            dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoa7,
                                      kTopEarlgreyPinmuxOutselConstantHighZ),
        [kDtSpiDevicePinctrlInputSck] = -1,
        [kDtSpiDevicePinctrlInputCsb] = -1,
        [kDtSpiDevicePinctrlInoutSd0] = -1,
        [kDtSpiDevicePinctrlInoutSd1] = -1,
        [kDtSpiDevicePinctrlInoutSd2] = -1,
        [kDtSpiDevicePinctrlInoutSd3] = -1,
};

static const dt_pinctrl_cfg_t
    periphmux_spi_device[kDtSpiDevicePinctrlInputCount] = {
        [kDtSpiDevicePinctrlInputTpmCsb] = dt_pinctrl_cfg_from_parts(
            kTopEarlgreyPinmuxPeripheralInSpiDeviceTpmCsb,
            kTopEarlgreyPinmuxInselIoa7),
        [kDtSpiDevicePinctrlInputSck] = -1,
        [kDtSpiDevicePinctrlInputCsb] = -1,
        [kDtSpiDevicePinctrlInoutSd0] = -1,
        [kDtSpiDevicePinctrlInoutSd1] = -1,
        [kDtSpiDevicePinctrlInoutSd2] = -1,
        [kDtSpiDevicePinctrlInoutSd3] = -1,
};

dt_pinctrl_cfg_t dt_pinctrl_get_padmux_config(dt_device_t dev, uint32_t idx) {
  switch (dev) {
    case kDtDeviceIdUart0:
    case kDtDeviceIdUart1:
    case kDtDeviceIdUart2:
    case kDtDeviceIdUart3:
      if (idx < kDtUartPinctrlOutputCount) {
        return padmux_uart[dev - kDtDeviceIdBaseUart][idx];
      }
      break;
    case kDtDeviceIdSpiDevice:
      if (idx < kDtSpiDevicePinctrlOutputCount) {
        return padmux_spi_device[idx];
      }
      break;
    case kDtDeviceIdI2c0:
    case kDtDeviceIdI2c1:
    case kDtDeviceIdI2c2:
      if (idx < kDtI2cPinctrlOutputCount) {
        return padmux_i2c[dev - kDtDeviceIdBaseI2c][idx];
      }
      break;
    case kDtDeviceIdSpiHost0:
      return -1;
    case kDtDeviceIdSpiHost1:
      if (idx < kDtSpiHostPinctrlOutputCount) {
        return padmux_spi_host1[idx];
      }
      break;
    case kDtDeviceIdUsbdev:
      if (idx < kDtUsbdevPinctrlOutputCount) {
        return padmux_usbdev[idx];
      }
      break;
    case kDtDeviceIdSysrstCtrlAon:
      if (idx < kDtSysrstCtrlPinctrlOutputCount) {
        return padmux_sysrst_ctrl[idx];
      }
      break;
    case kDtDeviceIdPwmAon:
      if (idx < kDtPwmPinctrlOutputCount) {
        return padmux_pwm[idx];
      }
      break;
    default:
      break;
  }
  return -1;
}

dt_pinctrl_cfg_t dt_pinctrl_get_periphmux_config(dt_device_t dev,
                                                 uint32_t idx) {
  switch (dev) {
    case kDtDeviceIdUart0:
    case kDtDeviceIdUart1:
    case kDtDeviceIdUart2:
    case kDtDeviceIdUart3:
      if (idx < kDtUartPinctrlInputCount) {
        return periphmux_uart[dev - kDtDeviceIdBaseUart][idx];
      }
      break;
    case kDtDeviceIdSpiDevice:
      if (idx < kDtSpiDevicePinctrlInputCount) {
        return periphmux_spi_device[idx];
      }
      break;
    case kDtDeviceIdI2c0:
    case kDtDeviceIdI2c1:
    case kDtDeviceIdI2c2:
      if (idx < kDtI2cPinctrlInputCount) {
        return periphmux_i2c[dev - kDtDeviceIdBaseI2c][idx];
      }
      break;
    case kDtDeviceIdSpiHost0:
      return -1;
    case kDtDeviceIdSpiHost1:
      if (idx < kDtSpiHostPinctrlInputCount) {
        return periphmux_spi_host1[idx];
      }
      break;
    case kDtDeviceIdUsbdev:
      if (idx < kDtUsbdevPinctrlInputCount) {
        return periphmux_usbdev[idx];
      }
      break;
    case kDtDeviceIdSysrstCtrlAon:
      if (idx < kDtSysrstCtrlPinctrlInputCount) {
        return periphmux_sysrst_ctrl[idx];
      }
      break;
    default:
      break;
  }
  return -1;
}

static const dt_pinctrl_cfg_t boot_padmux_cfgs[] = {
    // SW Straps
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc0,
                              kTopEarlgreyPinmuxOutselConstantHighZ),
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc1,
                              kTopEarlgreyPinmuxOutselConstantHighZ),
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc2,
                              kTopEarlgreyPinmuxOutselConstantHighZ),
    // ROM Console
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc4,
                              kTopEarlgreyPinmuxOutselUart0Tx),
    // Usbdev sense
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxMioOutIoc7,
                              kTopEarlgreyPinmuxOutselConstantHighZ),
};

static const dt_pinctrl_cfg_t boot_periphmux_cfgs[] = {
    // SW Straps
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxPeripheralInGpioGpio22,
                              kTopEarlgreyPinmuxInselIoc0),
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxPeripheralInGpioGpio23,
                              kTopEarlgreyPinmuxInselIoc1),
    dt_pinctrl_cfg_from_parts(kTopEarlgreyPinmuxPeripheralInGpioGpio24,
                              kTopEarlgreyPinmuxInselIoc2),
};

uint32_t dt_pinctrl_boot_padmux_config_len(void) {
  //  return ARRAYSIZE(boot_padmux_cfgs);
  return 5;
}

uint32_t dt_pinctrl_boot_periphmux_config_len(void) { return 3; }

dt_pinctrl_cfg_t dt_pinctrl_get_boot_padmux_config(uint32_t idx) {
  //  const uint32_t cfg_len = ARRAYSIZE(boot_padmux_cfgs);
  //  if (idx < cfg_len) {
  if (idx < 5) {
    return boot_padmux_cfgs[idx];
  }
  return -1;
}

dt_pinctrl_cfg_t dt_pinctrl_get_boot_periphmux_config(uint32_t idx) {
  //  const uint32_t cfg_len = ARRAYSIZE(boot_periphmux_cfgs);
  //  if (idx < cfg_len) {
  if (idx < 3) {
    return boot_periphmux_cfgs[idx];
  }
  return -1;
}
