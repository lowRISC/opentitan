// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// Note: these definitions rely on constants from top_earlgrey.h
// and therefore this library cannot be used with the `ujson_rust`
// bazel rule.  Instead, these constants are imported into rust
// by way of a bindgen rule and recreated as Rust datatypes with
// appropriate aliases to be used by other `ujson` libraries.
#ifndef RUST_PREPROCESSOR_EMIT
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#endif
// clang-format off

#define TOP_EARLGREY_PINMUX_PERIPHERAL_IN(_, value) \
    value(_, GpioGpio0, kTopEarlgreyPinmuxPeripheralInGpioGpio0) \
    value(_, GpioGpio1, kTopEarlgreyPinmuxPeripheralInGpioGpio1) \
    value(_, GpioGpio2, kTopEarlgreyPinmuxPeripheralInGpioGpio2) \
    value(_, GpioGpio3, kTopEarlgreyPinmuxPeripheralInGpioGpio3) \
    value(_, GpioGpio4, kTopEarlgreyPinmuxPeripheralInGpioGpio4) \
    value(_, GpioGpio5, kTopEarlgreyPinmuxPeripheralInGpioGpio5) \
    value(_, GpioGpio6, kTopEarlgreyPinmuxPeripheralInGpioGpio6) \
    value(_, GpioGpio7, kTopEarlgreyPinmuxPeripheralInGpioGpio7) \
    value(_, GpioGpio8, kTopEarlgreyPinmuxPeripheralInGpioGpio8) \
    value(_, GpioGpio9, kTopEarlgreyPinmuxPeripheralInGpioGpio9) \
    value(_, GpioGpio10, kTopEarlgreyPinmuxPeripheralInGpioGpio10) \
    value(_, GpioGpio11, kTopEarlgreyPinmuxPeripheralInGpioGpio11) \
    value(_, GpioGpio12, kTopEarlgreyPinmuxPeripheralInGpioGpio12) \
    value(_, GpioGpio13, kTopEarlgreyPinmuxPeripheralInGpioGpio13) \
    value(_, GpioGpio14, kTopEarlgreyPinmuxPeripheralInGpioGpio14) \
    value(_, GpioGpio15, kTopEarlgreyPinmuxPeripheralInGpioGpio15) \
    value(_, GpioGpio16, kTopEarlgreyPinmuxPeripheralInGpioGpio16) \
    value(_, GpioGpio17, kTopEarlgreyPinmuxPeripheralInGpioGpio17) \
    value(_, GpioGpio18, kTopEarlgreyPinmuxPeripheralInGpioGpio18) \
    value(_, GpioGpio19, kTopEarlgreyPinmuxPeripheralInGpioGpio19) \
    value(_, GpioGpio20, kTopEarlgreyPinmuxPeripheralInGpioGpio20) \
    value(_, GpioGpio21, kTopEarlgreyPinmuxPeripheralInGpioGpio21) \
    value(_, GpioGpio22, kTopEarlgreyPinmuxPeripheralInGpioGpio22) \
    value(_, GpioGpio23, kTopEarlgreyPinmuxPeripheralInGpioGpio23) \
    value(_, GpioGpio24, kTopEarlgreyPinmuxPeripheralInGpioGpio24) \
    value(_, GpioGpio25, kTopEarlgreyPinmuxPeripheralInGpioGpio25) \
    value(_, GpioGpio26, kTopEarlgreyPinmuxPeripheralInGpioGpio26) \
    value(_, GpioGpio27, kTopEarlgreyPinmuxPeripheralInGpioGpio27) \
    value(_, GpioGpio28, kTopEarlgreyPinmuxPeripheralInGpioGpio28) \
    value(_, GpioGpio29, kTopEarlgreyPinmuxPeripheralInGpioGpio29) \
    value(_, GpioGpio30, kTopEarlgreyPinmuxPeripheralInGpioGpio30) \
    value(_, GpioGpio31, kTopEarlgreyPinmuxPeripheralInGpioGpio31) \
    value(_, I2c0Sda, kTopEarlgreyPinmuxPeripheralInI2c0Sda) \
    value(_, I2c0Scl, kTopEarlgreyPinmuxPeripheralInI2c0Scl) \
    value(_, I2c1Sda, kTopEarlgreyPinmuxPeripheralInI2c1Sda) \
    value(_, I2c1Scl, kTopEarlgreyPinmuxPeripheralInI2c1Scl) \
    value(_, I2c2Sda, kTopEarlgreyPinmuxPeripheralInI2c2Sda) \
    value(_, I2c2Scl, kTopEarlgreyPinmuxPeripheralInI2c2Scl) \
    value(_, SpiHost1Sd0, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0) \
    value(_, SpiHost1Sd1, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1) \
    value(_, SpiHost1Sd2, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2) \
    value(_, SpiHost1Sd3, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3) \
    value(_, Uart0Rx, kTopEarlgreyPinmuxPeripheralInUart0Rx) \
    value(_, Uart1Rx, kTopEarlgreyPinmuxPeripheralInUart1Rx) \
    value(_, Uart2Rx, kTopEarlgreyPinmuxPeripheralInUart2Rx) \
    value(_, Uart3Rx, kTopEarlgreyPinmuxPeripheralInUart3Rx) \
    value(_, SpiDeviceTpmCsb, kTopEarlgreyPinmuxPeripheralInSpiDeviceTpmCsb) \
    value(_, FlashCtrlTck, kTopEarlgreyPinmuxPeripheralInFlashCtrlTck) \
    value(_, FlashCtrlTms, kTopEarlgreyPinmuxPeripheralInFlashCtrlTms) \
    value(_, FlashCtrlTdi, kTopEarlgreyPinmuxPeripheralInFlashCtrlTdi) \
    value(_, SysrstCtrlAonAcPresent, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent) \
    value(_, SysrstCtrlAonKey0In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In) \
    value(_, SysrstCtrlAonKey1In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In) \
    value(_, SysrstCtrlAonKey2In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In) \
    value(_, SysrstCtrlAonPwrbIn, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn) \
    value(_, SysrstCtrlAonLidOpen, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen) \
    value(_, UsbdevSense, kTopEarlgreyPinmuxPeripheralInUsbdevSense) \
    value(_, End, kTopEarlgreyPinmuxPeripheralInLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxPeripheralIn, pinmux_peripheral_in_t, TOP_EARLGREY_PINMUX_PERIPHERAL_IN, WITH_UNKNOWN));

#define TOP_EARLGREY_PINMUX_INSEL(_, value) \
    value(_, ConstantZero, kTopEarlgreyPinmuxInselConstantZero) \
    value(_, ConstantOne, kTopEarlgreyPinmuxInselConstantOne) \
    value(_, Ioa0, kTopEarlgreyPinmuxInselIoa0) \
    value(_, Ioa1, kTopEarlgreyPinmuxInselIoa1) \
    value(_, Ioa2, kTopEarlgreyPinmuxInselIoa2) \
    value(_, Ioa3, kTopEarlgreyPinmuxInselIoa3) \
    value(_, Ioa4, kTopEarlgreyPinmuxInselIoa4) \
    value(_, Ioa5, kTopEarlgreyPinmuxInselIoa5) \
    value(_, Ioa6, kTopEarlgreyPinmuxInselIoa6) \
    value(_, Ioa7, kTopEarlgreyPinmuxInselIoa7) \
    value(_, Ioa8, kTopEarlgreyPinmuxInselIoa8) \
    value(_, Iob0, kTopEarlgreyPinmuxInselIob0) \
    value(_, Iob1, kTopEarlgreyPinmuxInselIob1) \
    value(_, Iob2, kTopEarlgreyPinmuxInselIob2) \
    value(_, Iob3, kTopEarlgreyPinmuxInselIob3) \
    value(_, Iob4, kTopEarlgreyPinmuxInselIob4) \
    value(_, Iob5, kTopEarlgreyPinmuxInselIob5) \
    value(_, Iob6, kTopEarlgreyPinmuxInselIob6) \
    value(_, Iob7, kTopEarlgreyPinmuxInselIob7) \
    value(_, Iob8, kTopEarlgreyPinmuxInselIob8) \
    value(_, Iob9, kTopEarlgreyPinmuxInselIob9) \
    value(_, Iob10, kTopEarlgreyPinmuxInselIob10) \
    value(_, Iob11, kTopEarlgreyPinmuxInselIob11) \
    value(_, Iob12, kTopEarlgreyPinmuxInselIob12) \
    value(_, Ioc0, kTopEarlgreyPinmuxInselIoc0) \
    value(_, Ioc1, kTopEarlgreyPinmuxInselIoc1) \
    value(_, Ioc2, kTopEarlgreyPinmuxInselIoc2) \
    value(_, Ioc3, kTopEarlgreyPinmuxInselIoc3) \
    value(_, Ioc4, kTopEarlgreyPinmuxInselIoc4) \
    value(_, Ioc5, kTopEarlgreyPinmuxInselIoc5) \
    value(_, Ioc6, kTopEarlgreyPinmuxInselIoc6) \
    value(_, Ioc7, kTopEarlgreyPinmuxInselIoc7) \
    value(_, Ioc8, kTopEarlgreyPinmuxInselIoc8) \
    value(_, Ioc9, kTopEarlgreyPinmuxInselIoc9) \
    value(_, Ioc10, kTopEarlgreyPinmuxInselIoc10) \
    value(_, Ioc11, kTopEarlgreyPinmuxInselIoc11) \
    value(_, Ioc12, kTopEarlgreyPinmuxInselIoc12) \
    value(_, Ior0, kTopEarlgreyPinmuxInselIor0) \
    value(_, Ior1, kTopEarlgreyPinmuxInselIor1) \
    value(_, Ior2, kTopEarlgreyPinmuxInselIor2) \
    value(_, Ior3, kTopEarlgreyPinmuxInselIor3) \
    value(_, Ior4, kTopEarlgreyPinmuxInselIor4) \
    value(_, Ior5, kTopEarlgreyPinmuxInselIor5) \
    value(_, Ior6, kTopEarlgreyPinmuxInselIor6) \
    value(_, Ior7, kTopEarlgreyPinmuxInselIor7) \
    value(_, Ior10, kTopEarlgreyPinmuxInselIor10) \
    value(_, Ior11, kTopEarlgreyPinmuxInselIor11) \
    value(_, Ior12, kTopEarlgreyPinmuxInselIor12) \
    value(_, Ior13, kTopEarlgreyPinmuxInselIor13) \
    value(_, End, kTopEarlgreyPinmuxInselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxInsel, pinmux_insel_t, TOP_EARLGREY_PINMUX_INSEL, WITH_UNKNOWN));

#define TOP_EARLGREY_PINMUX_MIO_OUT(_, value) \
    value(_, Ioa0, kTopEarlgreyPinmuxMioOutIoa0) \
    value(_, Ioa1, kTopEarlgreyPinmuxMioOutIoa1) \
    value(_, Ioa2, kTopEarlgreyPinmuxMioOutIoa2) \
    value(_, Ioa3, kTopEarlgreyPinmuxMioOutIoa3) \
    value(_, Ioa4, kTopEarlgreyPinmuxMioOutIoa4) \
    value(_, Ioa5, kTopEarlgreyPinmuxMioOutIoa5) \
    value(_, Ioa6, kTopEarlgreyPinmuxMioOutIoa6) \
    value(_, Ioa7, kTopEarlgreyPinmuxMioOutIoa7) \
    value(_, Ioa8, kTopEarlgreyPinmuxMioOutIoa8) \
    value(_, Iob0, kTopEarlgreyPinmuxMioOutIob0) \
    value(_, Iob1, kTopEarlgreyPinmuxMioOutIob1) \
    value(_, Iob2, kTopEarlgreyPinmuxMioOutIob2) \
    value(_, Iob3, kTopEarlgreyPinmuxMioOutIob3) \
    value(_, Iob4, kTopEarlgreyPinmuxMioOutIob4) \
    value(_, Iob5, kTopEarlgreyPinmuxMioOutIob5) \
    value(_, Iob6, kTopEarlgreyPinmuxMioOutIob6) \
    value(_, Iob7, kTopEarlgreyPinmuxMioOutIob7) \
    value(_, Iob8, kTopEarlgreyPinmuxMioOutIob8) \
    value(_, Iob9, kTopEarlgreyPinmuxMioOutIob9) \
    value(_, Iob10, kTopEarlgreyPinmuxMioOutIob10) \
    value(_, Iob11, kTopEarlgreyPinmuxMioOutIob11) \
    value(_, Iob12, kTopEarlgreyPinmuxMioOutIob12) \
    value(_, Ioc0, kTopEarlgreyPinmuxMioOutIoc0) \
    value(_, Ioc1, kTopEarlgreyPinmuxMioOutIoc1) \
    value(_, Ioc2, kTopEarlgreyPinmuxMioOutIoc2) \
    value(_, Ioc3, kTopEarlgreyPinmuxMioOutIoc3) \
    value(_, Ioc4, kTopEarlgreyPinmuxMioOutIoc4) \
    value(_, Ioc5, kTopEarlgreyPinmuxMioOutIoc5) \
    value(_, Ioc6, kTopEarlgreyPinmuxMioOutIoc6) \
    value(_, Ioc7, kTopEarlgreyPinmuxMioOutIoc7) \
    value(_, Ioc8, kTopEarlgreyPinmuxMioOutIoc8) \
    value(_, Ioc9, kTopEarlgreyPinmuxMioOutIoc9) \
    value(_, Ioc10, kTopEarlgreyPinmuxMioOutIoc10) \
    value(_, Ioc11, kTopEarlgreyPinmuxMioOutIoc11) \
    value(_, Ioc12, kTopEarlgreyPinmuxMioOutIoc12) \
    value(_, Ior0, kTopEarlgreyPinmuxMioOutIor0) \
    value(_, Ior1, kTopEarlgreyPinmuxMioOutIor1) \
    value(_, Ior2, kTopEarlgreyPinmuxMioOutIor2) \
    value(_, Ior3, kTopEarlgreyPinmuxMioOutIor3) \
    value(_, Ior4, kTopEarlgreyPinmuxMioOutIor4) \
    value(_, Ior5, kTopEarlgreyPinmuxMioOutIor5) \
    value(_, Ior6, kTopEarlgreyPinmuxMioOutIor6) \
    value(_, Ior7, kTopEarlgreyPinmuxMioOutIor7) \
    value(_, Ior10, kTopEarlgreyPinmuxMioOutIor10) \
    value(_, Ior11, kTopEarlgreyPinmuxMioOutIor11) \
    value(_, Ior12, kTopEarlgreyPinmuxMioOutIor12) \
    value(_, Ior13, kTopEarlgreyPinmuxMioOutIor13) \
    value(_, End, kTopEarlgreyPinmuxMioOutLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxMioOut, pinmux_mio_out_t, TOP_EARLGREY_PINMUX_MIO_OUT, WITH_UNKNOWN));

#define TOP_EARLGREY_PINMUX_OUTSEL(_, value) \
    value(_, ConstantZero, kTopEarlgreyPinmuxOutselConstantZero) \
    value(_, ConstantOne, kTopEarlgreyPinmuxOutselConstantOne) \
    value(_, ConstantHighZ, kTopEarlgreyPinmuxOutselConstantHighZ) \
    value(_, GpioGpio0, kTopEarlgreyPinmuxOutselGpioGpio0) \
    value(_, GpioGpio1, kTopEarlgreyPinmuxOutselGpioGpio1) \
    value(_, GpioGpio2, kTopEarlgreyPinmuxOutselGpioGpio2) \
    value(_, GpioGpio3, kTopEarlgreyPinmuxOutselGpioGpio3) \
    value(_, GpioGpio4, kTopEarlgreyPinmuxOutselGpioGpio4) \
    value(_, GpioGpio5, kTopEarlgreyPinmuxOutselGpioGpio5) \
    value(_, GpioGpio6, kTopEarlgreyPinmuxOutselGpioGpio6) \
    value(_, GpioGpio7, kTopEarlgreyPinmuxOutselGpioGpio7) \
    value(_, GpioGpio8, kTopEarlgreyPinmuxOutselGpioGpio8) \
    value(_, GpioGpio9, kTopEarlgreyPinmuxOutselGpioGpio9) \
    value(_, GpioGpio10, kTopEarlgreyPinmuxOutselGpioGpio10) \
    value(_, GpioGpio11, kTopEarlgreyPinmuxOutselGpioGpio11) \
    value(_, GpioGpio12, kTopEarlgreyPinmuxOutselGpioGpio12) \
    value(_, GpioGpio13, kTopEarlgreyPinmuxOutselGpioGpio13) \
    value(_, GpioGpio14, kTopEarlgreyPinmuxOutselGpioGpio14) \
    value(_, GpioGpio15, kTopEarlgreyPinmuxOutselGpioGpio15) \
    value(_, GpioGpio16, kTopEarlgreyPinmuxOutselGpioGpio16) \
    value(_, GpioGpio17, kTopEarlgreyPinmuxOutselGpioGpio17) \
    value(_, GpioGpio18, kTopEarlgreyPinmuxOutselGpioGpio18) \
    value(_, GpioGpio19, kTopEarlgreyPinmuxOutselGpioGpio19) \
    value(_, GpioGpio20, kTopEarlgreyPinmuxOutselGpioGpio20) \
    value(_, GpioGpio21, kTopEarlgreyPinmuxOutselGpioGpio21) \
    value(_, GpioGpio22, kTopEarlgreyPinmuxOutselGpioGpio22) \
    value(_, GpioGpio23, kTopEarlgreyPinmuxOutselGpioGpio23) \
    value(_, GpioGpio24, kTopEarlgreyPinmuxOutselGpioGpio24) \
    value(_, GpioGpio25, kTopEarlgreyPinmuxOutselGpioGpio25) \
    value(_, GpioGpio26, kTopEarlgreyPinmuxOutselGpioGpio26) \
    value(_, GpioGpio27, kTopEarlgreyPinmuxOutselGpioGpio27) \
    value(_, GpioGpio28, kTopEarlgreyPinmuxOutselGpioGpio28) \
    value(_, GpioGpio29, kTopEarlgreyPinmuxOutselGpioGpio29) \
    value(_, GpioGpio30, kTopEarlgreyPinmuxOutselGpioGpio30) \
    value(_, GpioGpio31, kTopEarlgreyPinmuxOutselGpioGpio31) \
    value(_, I2c0Sda, kTopEarlgreyPinmuxOutselI2c0Sda) \
    value(_, I2c0Scl, kTopEarlgreyPinmuxOutselI2c0Scl) \
    value(_, I2c1Sda, kTopEarlgreyPinmuxOutselI2c1Sda) \
    value(_, I2c1Scl, kTopEarlgreyPinmuxOutselI2c1Scl) \
    value(_, I2c2Sda, kTopEarlgreyPinmuxOutselI2c2Sda) \
    value(_, I2c2Scl, kTopEarlgreyPinmuxOutselI2c2Scl) \
    value(_, SpiHost1Sd0, kTopEarlgreyPinmuxOutselSpiHost1Sd0) \
    value(_, SpiHost1Sd1, kTopEarlgreyPinmuxOutselSpiHost1Sd1) \
    value(_, SpiHost1Sd2, kTopEarlgreyPinmuxOutselSpiHost1Sd2) \
    value(_, SpiHost1Sd3, kTopEarlgreyPinmuxOutselSpiHost1Sd3) \
    value(_, Uart0Tx, kTopEarlgreyPinmuxOutselUart0Tx) \
    value(_, Uart1Tx, kTopEarlgreyPinmuxOutselUart1Tx) \
    value(_, Uart2Tx, kTopEarlgreyPinmuxOutselUart2Tx) \
    value(_, Uart3Tx, kTopEarlgreyPinmuxOutselUart3Tx) \
    value(_, PattgenPda0Tx, kTopEarlgreyPinmuxOutselPattgenPda0Tx) \
    value(_, PattgenPcl0Tx, kTopEarlgreyPinmuxOutselPattgenPcl0Tx) \
    value(_, PattgenPda1Tx, kTopEarlgreyPinmuxOutselPattgenPda1Tx) \
    value(_, PattgenPcl1Tx, kTopEarlgreyPinmuxOutselPattgenPcl1Tx) \
    value(_, SpiHost1Sck, kTopEarlgreyPinmuxOutselSpiHost1Sck) \
    value(_, SpiHost1Csb, kTopEarlgreyPinmuxOutselSpiHost1Csb) \
    value(_, FlashCtrlTdo, kTopEarlgreyPinmuxOutselFlashCtrlTdo) \
    value(_, SensorCtrlAstDebugOut0, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut0) \
    value(_, SensorCtrlAstDebugOut1, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut1) \
    value(_, SensorCtrlAstDebugOut2, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut2) \
    value(_, SensorCtrlAstDebugOut3, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut3) \
    value(_, SensorCtrlAstDebugOut4, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut4) \
    value(_, SensorCtrlAstDebugOut5, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut5) \
    value(_, SensorCtrlAstDebugOut6, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut6) \
    value(_, SensorCtrlAstDebugOut7, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut7) \
    value(_, SensorCtrlAstDebugOut8, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut8) \
    value(_, PwmAonPwm0, kTopEarlgreyPinmuxOutselPwmAonPwm0) \
    value(_, PwmAonPwm1, kTopEarlgreyPinmuxOutselPwmAonPwm1) \
    value(_, PwmAonPwm2, kTopEarlgreyPinmuxOutselPwmAonPwm2) \
    value(_, PwmAonPwm3, kTopEarlgreyPinmuxOutselPwmAonPwm3) \
    value(_, PwmAonPwm4, kTopEarlgreyPinmuxOutselPwmAonPwm4) \
    value(_, PwmAonPwm5, kTopEarlgreyPinmuxOutselPwmAonPwm5) \
    value(_, OtpCtrlTest0, kTopEarlgreyPinmuxOutselOtpCtrlTest0) \
    value(_, SysrstCtrlAonBatDisable, kTopEarlgreyPinmuxOutselSysrstCtrlAonBatDisable) \
    value(_, SysrstCtrlAonKey0Out, kTopEarlgreyPinmuxOutselSysrstCtrlAonKey0Out) \
    value(_, SysrstCtrlAonKey1Out, kTopEarlgreyPinmuxOutselSysrstCtrlAonKey1Out) \
    value(_, SysrstCtrlAonKey2Out, kTopEarlgreyPinmuxOutselSysrstCtrlAonKey2Out) \
    value(_, SysrstCtrlAonPwrbOut, kTopEarlgreyPinmuxOutselSysrstCtrlAonPwrbOut) \
    value(_, SysrstCtrlAonZ3Wakeup, kTopEarlgreyPinmuxOutselSysrstCtrlAonZ3Wakeup) \
    value(_, End, kTopEarlgreyPinmuxOutselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxOutsel, pinmux_outsel_t, TOP_EARLGREY_PINMUX_OUTSEL, WITH_UNKNOWN));

#define TOP_EARLGREY_DIRECT_PADS(_, value) \
    value(_, UsbdevUsbDp, kTopEarlgreyDirectPadsUsbdevUsbDp) \
    value(_, UsbdevUsbDn, kTopEarlgreyDirectPadsUsbdevUsbDn) \
    value(_, SpiHost0Sd0, kTopEarlgreyDirectPadsSpiHost0Sd0) \
    value(_, SpiHost0Sd1, kTopEarlgreyDirectPadsSpiHost0Sd1) \
    value(_, SpiHost0Sd2, kTopEarlgreyDirectPadsSpiHost0Sd2) \
    value(_, SpiHost0Sd3, kTopEarlgreyDirectPadsSpiHost0Sd3) \
    value(_, SpiDeviceSd0, kTopEarlgreyDirectPadsSpiDeviceSd0) \
    value(_, SpiDeviceSd1, kTopEarlgreyDirectPadsSpiDeviceSd1) \
    value(_, SpiDeviceSd2, kTopEarlgreyDirectPadsSpiDeviceSd2) \
    value(_, SpiDeviceSd3, kTopEarlgreyDirectPadsSpiDeviceSd3) \
    value(_, SysrstCtrlAonEcRstL, kTopEarlgreyDirectPadsSysrstCtrlAonEcRstL) \
    value(_, SysrstCtrlAonFlashWpL, kTopEarlgreyDirectPadsSysrstCtrlAonFlashWpL) \
    value(_, SpiDeviceSck, kTopEarlgreyDirectPadsSpiDeviceSck) \
    value(_, SpiDeviceCsb, kTopEarlgreyDirectPadsSpiDeviceCsb) \
    value(_, SpiHost0Sck, kTopEarlgreyDirectPadsSpiHost0Sck) \
    value(_, SpiHost0Csb, kTopEarlgreyDirectPadsSpiHost0Csb) \
    value(_, End, kTopEarlgreyDirectPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(DirectPads, direct_pads_t, TOP_EARLGREY_DIRECT_PADS, WITH_UNKNOWN));

#define TOP_EARLGREY_MUXED_PADS(_, value) \
    value(_, Ioa0, kTopEarlgreyMuxedPadsIoa0) \
    value(_, Ioa1, kTopEarlgreyMuxedPadsIoa1) \
    value(_, Ioa2, kTopEarlgreyMuxedPadsIoa2) \
    value(_, Ioa3, kTopEarlgreyMuxedPadsIoa3) \
    value(_, Ioa4, kTopEarlgreyMuxedPadsIoa4) \
    value(_, Ioa5, kTopEarlgreyMuxedPadsIoa5) \
    value(_, Ioa6, kTopEarlgreyMuxedPadsIoa6) \
    value(_, Ioa7, kTopEarlgreyMuxedPadsIoa7) \
    value(_, Ioa8, kTopEarlgreyMuxedPadsIoa8) \
    value(_, Iob0, kTopEarlgreyMuxedPadsIob0) \
    value(_, Iob1, kTopEarlgreyMuxedPadsIob1) \
    value(_, Iob2, kTopEarlgreyMuxedPadsIob2) \
    value(_, Iob3, kTopEarlgreyMuxedPadsIob3) \
    value(_, Iob4, kTopEarlgreyMuxedPadsIob4) \
    value(_, Iob5, kTopEarlgreyMuxedPadsIob5) \
    value(_, Iob6, kTopEarlgreyMuxedPadsIob6) \
    value(_, Iob7, kTopEarlgreyMuxedPadsIob7) \
    value(_, Iob8, kTopEarlgreyMuxedPadsIob8) \
    value(_, Iob9, kTopEarlgreyMuxedPadsIob9) \
    value(_, Iob10, kTopEarlgreyMuxedPadsIob10) \
    value(_, Iob11, kTopEarlgreyMuxedPadsIob11) \
    value(_, Iob12, kTopEarlgreyMuxedPadsIob12) \
    value(_, Ioc0, kTopEarlgreyMuxedPadsIoc0) \
    value(_, Ioc1, kTopEarlgreyMuxedPadsIoc1) \
    value(_, Ioc2, kTopEarlgreyMuxedPadsIoc2) \
    value(_, Ioc3, kTopEarlgreyMuxedPadsIoc3) \
    value(_, Ioc4, kTopEarlgreyMuxedPadsIoc4) \
    value(_, Ioc5, kTopEarlgreyMuxedPadsIoc5) \
    value(_, Ioc6, kTopEarlgreyMuxedPadsIoc6) \
    value(_, Ioc7, kTopEarlgreyMuxedPadsIoc7) \
    value(_, Ioc8, kTopEarlgreyMuxedPadsIoc8) \
    value(_, Ioc9, kTopEarlgreyMuxedPadsIoc9) \
    value(_, Ioc10, kTopEarlgreyMuxedPadsIoc10) \
    value(_, Ioc11, kTopEarlgreyMuxedPadsIoc11) \
    value(_, Ioc12, kTopEarlgreyMuxedPadsIoc12) \
    value(_, Ior0, kTopEarlgreyMuxedPadsIor0) \
    value(_, Ior1, kTopEarlgreyMuxedPadsIor1) \
    value(_, Ior2, kTopEarlgreyMuxedPadsIor2) \
    value(_, Ior3, kTopEarlgreyMuxedPadsIor3) \
    value(_, Ior4, kTopEarlgreyMuxedPadsIor4) \
    value(_, Ior5, kTopEarlgreyMuxedPadsIor5) \
    value(_, Ior6, kTopEarlgreyMuxedPadsIor6) \
    value(_, Ior7, kTopEarlgreyMuxedPadsIor7) \
    value(_, Ior10, kTopEarlgreyMuxedPadsIor10) \
    value(_, Ior11, kTopEarlgreyMuxedPadsIor11) \
    value(_, Ior12, kTopEarlgreyMuxedPadsIor12) \
    value(_, Ior13, kTopEarlgreyMuxedPadsIor13) \
    value(_, End, kTopEarlgreyMuxedPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(MuxedPads, muxed_pads_t, TOP_EARLGREY_MUXED_PADS, WITH_UNKNOWN));

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
