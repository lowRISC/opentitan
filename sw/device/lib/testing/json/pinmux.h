// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
#include "sw/lib/sw/device/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// Note: these definitions rely on constants from top_darjeeling.h
// and therefore this library cannot be used with the `ujson_rust`
// bazel rule.  Instead, these constants are imported into rust
// by way of a bindgen rule and recreated as Rust datatypes with
// appropriate aliases to be used by other `ujson` libraries.
#ifndef RUST_PREPROCESSOR_EMIT
#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#endif
// clang-format off

#define TOP_DARJEELING_PINMUX_PERIPHERAL_IN(_, value) \
    value(_, GpioGpio0, kTopDarjeelingPinmuxPeripheralInGpioGpio0) \
    value(_, GpioGpio1, kTopDarjeelingPinmuxPeripheralInGpioGpio1) \
    value(_, GpioGpio2, kTopDarjeelingPinmuxPeripheralInGpioGpio2) \
    value(_, GpioGpio3, kTopDarjeelingPinmuxPeripheralInGpioGpio3) \
    value(_, GpioGpio4, kTopDarjeelingPinmuxPeripheralInGpioGpio4) \
    value(_, GpioGpio5, kTopDarjeelingPinmuxPeripheralInGpioGpio5) \
    value(_, GpioGpio6, kTopDarjeelingPinmuxPeripheralInGpioGpio6) \
    value(_, GpioGpio7, kTopDarjeelingPinmuxPeripheralInGpioGpio7) \
    value(_, GpioGpio8, kTopDarjeelingPinmuxPeripheralInGpioGpio8) \
    value(_, GpioGpio9, kTopDarjeelingPinmuxPeripheralInGpioGpio9) \
    value(_, GpioGpio10, kTopDarjeelingPinmuxPeripheralInGpioGpio10) \
    value(_, GpioGpio11, kTopDarjeelingPinmuxPeripheralInGpioGpio11) \
    value(_, GpioGpio12, kTopDarjeelingPinmuxPeripheralInGpioGpio12) \
    value(_, GpioGpio13, kTopDarjeelingPinmuxPeripheralInGpioGpio13) \
    value(_, GpioGpio14, kTopDarjeelingPinmuxPeripheralInGpioGpio14) \
    value(_, GpioGpio15, kTopDarjeelingPinmuxPeripheralInGpioGpio15) \
    value(_, GpioGpio16, kTopDarjeelingPinmuxPeripheralInGpioGpio16) \
    value(_, GpioGpio17, kTopDarjeelingPinmuxPeripheralInGpioGpio17) \
    value(_, GpioGpio18, kTopDarjeelingPinmuxPeripheralInGpioGpio18) \
    value(_, GpioGpio19, kTopDarjeelingPinmuxPeripheralInGpioGpio19) \
    value(_, GpioGpio20, kTopDarjeelingPinmuxPeripheralInGpioGpio20) \
    value(_, GpioGpio21, kTopDarjeelingPinmuxPeripheralInGpioGpio21) \
    value(_, GpioGpio22, kTopDarjeelingPinmuxPeripheralInGpioGpio22) \
    value(_, GpioGpio23, kTopDarjeelingPinmuxPeripheralInGpioGpio23) \
    value(_, GpioGpio24, kTopDarjeelingPinmuxPeripheralInGpioGpio24) \
    value(_, GpioGpio25, kTopDarjeelingPinmuxPeripheralInGpioGpio25) \
    value(_, GpioGpio26, kTopDarjeelingPinmuxPeripheralInGpioGpio26) \
    value(_, GpioGpio27, kTopDarjeelingPinmuxPeripheralInGpioGpio27) \
    value(_, GpioGpio28, kTopDarjeelingPinmuxPeripheralInGpioGpio28) \
    value(_, GpioGpio29, kTopDarjeelingPinmuxPeripheralInGpioGpio29) \
    value(_, GpioGpio30, kTopDarjeelingPinmuxPeripheralInGpioGpio30) \
    value(_, GpioGpio31, kTopDarjeelingPinmuxPeripheralInGpioGpio31) \
    value(_, I2c0Sda, kTopDarjeelingPinmuxPeripheralInI2c0Sda) \
    value(_, I2c0Scl, kTopDarjeelingPinmuxPeripheralInI2c0Scl) \
    value(_, I2c1Sda, kTopDarjeelingPinmuxPeripheralInI2c1Sda) \
    value(_, I2c1Scl, kTopDarjeelingPinmuxPeripheralInI2c1Scl) \
    value(_, I2c2Sda, kTopDarjeelingPinmuxPeripheralInI2c2Sda) \
    value(_, I2c2Scl, kTopDarjeelingPinmuxPeripheralInI2c2Scl) \
    value(_, SpiHost1Sd0, kTopDarjeelingPinmuxPeripheralInSpiHost1Sd0) \
    value(_, SpiHost1Sd1, kTopDarjeelingPinmuxPeripheralInSpiHost1Sd1) \
    value(_, SpiHost1Sd2, kTopDarjeelingPinmuxPeripheralInSpiHost1Sd2) \
    value(_, SpiHost1Sd3, kTopDarjeelingPinmuxPeripheralInSpiHost1Sd3) \
    value(_, Uart0Rx, kTopDarjeelingPinmuxPeripheralInUart0Rx) \
    value(_, Uart1Rx, kTopDarjeelingPinmuxPeripheralInUart1Rx) \
    value(_, Uart2Rx, kTopDarjeelingPinmuxPeripheralInUart2Rx) \
    value(_, Uart3Rx, kTopDarjeelingPinmuxPeripheralInUart3Rx) \
    value(_, SpiDeviceTpmCsb, kTopDarjeelingPinmuxPeripheralInSpiDeviceTpmCsb) \
    value(_, FlashCtrlTck, kTopDarjeelingPinmuxPeripheralInFlashCtrlTck) \
    value(_, FlashCtrlTms, kTopDarjeelingPinmuxPeripheralInFlashCtrlTms) \
    value(_, FlashCtrlTdi, kTopDarjeelingPinmuxPeripheralInFlashCtrlTdi) \
    value(_, SysrstCtrlAonAcPresent, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonAcPresent) \
    value(_, SysrstCtrlAonKey0In, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey0In) \
    value(_, SysrstCtrlAonKey1In, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey1In) \
    value(_, SysrstCtrlAonKey2In, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey2In) \
    value(_, SysrstCtrlAonPwrbIn, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonPwrbIn) \
    value(_, SysrstCtrlAonLidOpen, kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonLidOpen) \
    value(_, UsbdevSense, kTopDarjeelingPinmuxPeripheralInUsbdevSense) \
    value(_, End, kTopDarjeelingPinmuxPeripheralInLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxPeripheralIn, pinmux_peripheral_in_t, TOP_DARJEELING_PINMUX_PERIPHERAL_IN, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_INSEL(_, value) \
    value(_, ConstantZero, kTopDarjeelingPinmuxInselConstantZero) \
    value(_, ConstantOne, kTopDarjeelingPinmuxInselConstantOne) \
    value(_, Ioa0, kTopDarjeelingPinmuxInselIoa0) \
    value(_, Ioa1, kTopDarjeelingPinmuxInselIoa1) \
    value(_, Ioa2, kTopDarjeelingPinmuxInselIoa2) \
    value(_, Ioa3, kTopDarjeelingPinmuxInselIoa3) \
    value(_, Ioa4, kTopDarjeelingPinmuxInselIoa4) \
    value(_, Ioa5, kTopDarjeelingPinmuxInselIoa5) \
    value(_, Ioa6, kTopDarjeelingPinmuxInselIoa6) \
    value(_, Ioa7, kTopDarjeelingPinmuxInselIoa7) \
    value(_, Ioa8, kTopDarjeelingPinmuxInselIoa8) \
    value(_, Iob0, kTopDarjeelingPinmuxInselIob0) \
    value(_, Iob1, kTopDarjeelingPinmuxInselIob1) \
    value(_, Iob2, kTopDarjeelingPinmuxInselIob2) \
    value(_, Iob3, kTopDarjeelingPinmuxInselIob3) \
    value(_, Iob4, kTopDarjeelingPinmuxInselIob4) \
    value(_, Iob5, kTopDarjeelingPinmuxInselIob5) \
    value(_, Iob6, kTopDarjeelingPinmuxInselIob6) \
    value(_, Iob7, kTopDarjeelingPinmuxInselIob7) \
    value(_, Iob8, kTopDarjeelingPinmuxInselIob8) \
    value(_, Iob9, kTopDarjeelingPinmuxInselIob9) \
    value(_, Iob10, kTopDarjeelingPinmuxInselIob10) \
    value(_, Iob11, kTopDarjeelingPinmuxInselIob11) \
    value(_, Iob12, kTopDarjeelingPinmuxInselIob12) \
    value(_, Ioc0, kTopDarjeelingPinmuxInselIoc0) \
    value(_, Ioc1, kTopDarjeelingPinmuxInselIoc1) \
    value(_, Ioc2, kTopDarjeelingPinmuxInselIoc2) \
    value(_, Ioc3, kTopDarjeelingPinmuxInselIoc3) \
    value(_, Ioc4, kTopDarjeelingPinmuxInselIoc4) \
    value(_, Ioc5, kTopDarjeelingPinmuxInselIoc5) \
    value(_, Ioc6, kTopDarjeelingPinmuxInselIoc6) \
    value(_, Ioc7, kTopDarjeelingPinmuxInselIoc7) \
    value(_, Ioc8, kTopDarjeelingPinmuxInselIoc8) \
    value(_, Ioc9, kTopDarjeelingPinmuxInselIoc9) \
    value(_, Ioc10, kTopDarjeelingPinmuxInselIoc10) \
    value(_, Ioc11, kTopDarjeelingPinmuxInselIoc11) \
    value(_, Ioc12, kTopDarjeelingPinmuxInselIoc12) \
    value(_, Ior0, kTopDarjeelingPinmuxInselIor0) \
    value(_, Ior1, kTopDarjeelingPinmuxInselIor1) \
    value(_, Ior2, kTopDarjeelingPinmuxInselIor2) \
    value(_, Ior3, kTopDarjeelingPinmuxInselIor3) \
    value(_, Ior4, kTopDarjeelingPinmuxInselIor4) \
    value(_, Ior5, kTopDarjeelingPinmuxInselIor5) \
    value(_, Ior6, kTopDarjeelingPinmuxInselIor6) \
    value(_, Ior7, kTopDarjeelingPinmuxInselIor7) \
    value(_, Ior10, kTopDarjeelingPinmuxInselIor10) \
    value(_, Ior11, kTopDarjeelingPinmuxInselIor11) \
    value(_, Ior12, kTopDarjeelingPinmuxInselIor12) \
    value(_, Ior13, kTopDarjeelingPinmuxInselIor13) \
    value(_, End, kTopDarjeelingPinmuxInselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxInsel, pinmux_insel_t, TOP_DARJEELING_PINMUX_INSEL, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_MIO_OUT(_, value) \
    value(_, Ioa0, kTopDarjeelingPinmuxMioOutIoa0) \
    value(_, Ioa1, kTopDarjeelingPinmuxMioOutIoa1) \
    value(_, Ioa2, kTopDarjeelingPinmuxMioOutIoa2) \
    value(_, Ioa3, kTopDarjeelingPinmuxMioOutIoa3) \
    value(_, Ioa4, kTopDarjeelingPinmuxMioOutIoa4) \
    value(_, Ioa5, kTopDarjeelingPinmuxMioOutIoa5) \
    value(_, Ioa6, kTopDarjeelingPinmuxMioOutIoa6) \
    value(_, Ioa7, kTopDarjeelingPinmuxMioOutIoa7) \
    value(_, Ioa8, kTopDarjeelingPinmuxMioOutIoa8) \
    value(_, Iob0, kTopDarjeelingPinmuxMioOutIob0) \
    value(_, Iob1, kTopDarjeelingPinmuxMioOutIob1) \
    value(_, Iob2, kTopDarjeelingPinmuxMioOutIob2) \
    value(_, Iob3, kTopDarjeelingPinmuxMioOutIob3) \
    value(_, Iob4, kTopDarjeelingPinmuxMioOutIob4) \
    value(_, Iob5, kTopDarjeelingPinmuxMioOutIob5) \
    value(_, Iob6, kTopDarjeelingPinmuxMioOutIob6) \
    value(_, Iob7, kTopDarjeelingPinmuxMioOutIob7) \
    value(_, Iob8, kTopDarjeelingPinmuxMioOutIob8) \
    value(_, Iob9, kTopDarjeelingPinmuxMioOutIob9) \
    value(_, Iob10, kTopDarjeelingPinmuxMioOutIob10) \
    value(_, Iob11, kTopDarjeelingPinmuxMioOutIob11) \
    value(_, Iob12, kTopDarjeelingPinmuxMioOutIob12) \
    value(_, Ioc0, kTopDarjeelingPinmuxMioOutIoc0) \
    value(_, Ioc1, kTopDarjeelingPinmuxMioOutIoc1) \
    value(_, Ioc2, kTopDarjeelingPinmuxMioOutIoc2) \
    value(_, Ioc3, kTopDarjeelingPinmuxMioOutIoc3) \
    value(_, Ioc4, kTopDarjeelingPinmuxMioOutIoc4) \
    value(_, Ioc5, kTopDarjeelingPinmuxMioOutIoc5) \
    value(_, Ioc6, kTopDarjeelingPinmuxMioOutIoc6) \
    value(_, Ioc7, kTopDarjeelingPinmuxMioOutIoc7) \
    value(_, Ioc8, kTopDarjeelingPinmuxMioOutIoc8) \
    value(_, Ioc9, kTopDarjeelingPinmuxMioOutIoc9) \
    value(_, Ioc10, kTopDarjeelingPinmuxMioOutIoc10) \
    value(_, Ioc11, kTopDarjeelingPinmuxMioOutIoc11) \
    value(_, Ioc12, kTopDarjeelingPinmuxMioOutIoc12) \
    value(_, Ior0, kTopDarjeelingPinmuxMioOutIor0) \
    value(_, Ior1, kTopDarjeelingPinmuxMioOutIor1) \
    value(_, Ior2, kTopDarjeelingPinmuxMioOutIor2) \
    value(_, Ior3, kTopDarjeelingPinmuxMioOutIor3) \
    value(_, Ior4, kTopDarjeelingPinmuxMioOutIor4) \
    value(_, Ior5, kTopDarjeelingPinmuxMioOutIor5) \
    value(_, Ior6, kTopDarjeelingPinmuxMioOutIor6) \
    value(_, Ior7, kTopDarjeelingPinmuxMioOutIor7) \
    value(_, Ior10, kTopDarjeelingPinmuxMioOutIor10) \
    value(_, Ior11, kTopDarjeelingPinmuxMioOutIor11) \
    value(_, Ior12, kTopDarjeelingPinmuxMioOutIor12) \
    value(_, Ior13, kTopDarjeelingPinmuxMioOutIor13) \
    value(_, End, kTopDarjeelingPinmuxMioOutLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxMioOut, pinmux_mio_out_t, TOP_DARJEELING_PINMUX_MIO_OUT, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_OUTSEL(_, value) \
    value(_, ConstantZero, kTopDarjeelingPinmuxOutselConstantZero) \
    value(_, ConstantOne, kTopDarjeelingPinmuxOutselConstantOne) \
    value(_, ConstantHighZ, kTopDarjeelingPinmuxOutselConstantHighZ) \
    value(_, GpioGpio0, kTopDarjeelingPinmuxOutselGpioGpio0) \
    value(_, GpioGpio1, kTopDarjeelingPinmuxOutselGpioGpio1) \
    value(_, GpioGpio2, kTopDarjeelingPinmuxOutselGpioGpio2) \
    value(_, GpioGpio3, kTopDarjeelingPinmuxOutselGpioGpio3) \
    value(_, GpioGpio4, kTopDarjeelingPinmuxOutselGpioGpio4) \
    value(_, GpioGpio5, kTopDarjeelingPinmuxOutselGpioGpio5) \
    value(_, GpioGpio6, kTopDarjeelingPinmuxOutselGpioGpio6) \
    value(_, GpioGpio7, kTopDarjeelingPinmuxOutselGpioGpio7) \
    value(_, GpioGpio8, kTopDarjeelingPinmuxOutselGpioGpio8) \
    value(_, GpioGpio9, kTopDarjeelingPinmuxOutselGpioGpio9) \
    value(_, GpioGpio10, kTopDarjeelingPinmuxOutselGpioGpio10) \
    value(_, GpioGpio11, kTopDarjeelingPinmuxOutselGpioGpio11) \
    value(_, GpioGpio12, kTopDarjeelingPinmuxOutselGpioGpio12) \
    value(_, GpioGpio13, kTopDarjeelingPinmuxOutselGpioGpio13) \
    value(_, GpioGpio14, kTopDarjeelingPinmuxOutselGpioGpio14) \
    value(_, GpioGpio15, kTopDarjeelingPinmuxOutselGpioGpio15) \
    value(_, GpioGpio16, kTopDarjeelingPinmuxOutselGpioGpio16) \
    value(_, GpioGpio17, kTopDarjeelingPinmuxOutselGpioGpio17) \
    value(_, GpioGpio18, kTopDarjeelingPinmuxOutselGpioGpio18) \
    value(_, GpioGpio19, kTopDarjeelingPinmuxOutselGpioGpio19) \
    value(_, GpioGpio20, kTopDarjeelingPinmuxOutselGpioGpio20) \
    value(_, GpioGpio21, kTopDarjeelingPinmuxOutselGpioGpio21) \
    value(_, GpioGpio22, kTopDarjeelingPinmuxOutselGpioGpio22) \
    value(_, GpioGpio23, kTopDarjeelingPinmuxOutselGpioGpio23) \
    value(_, GpioGpio24, kTopDarjeelingPinmuxOutselGpioGpio24) \
    value(_, GpioGpio25, kTopDarjeelingPinmuxOutselGpioGpio25) \
    value(_, GpioGpio26, kTopDarjeelingPinmuxOutselGpioGpio26) \
    value(_, GpioGpio27, kTopDarjeelingPinmuxOutselGpioGpio27) \
    value(_, GpioGpio28, kTopDarjeelingPinmuxOutselGpioGpio28) \
    value(_, GpioGpio29, kTopDarjeelingPinmuxOutselGpioGpio29) \
    value(_, GpioGpio30, kTopDarjeelingPinmuxOutselGpioGpio30) \
    value(_, GpioGpio31, kTopDarjeelingPinmuxOutselGpioGpio31) \
    value(_, I2c0Sda, kTopDarjeelingPinmuxOutselI2c0Sda) \
    value(_, I2c0Scl, kTopDarjeelingPinmuxOutselI2c0Scl) \
    value(_, I2c1Sda, kTopDarjeelingPinmuxOutselI2c1Sda) \
    value(_, I2c1Scl, kTopDarjeelingPinmuxOutselI2c1Scl) \
    value(_, I2c2Sda, kTopDarjeelingPinmuxOutselI2c2Sda) \
    value(_, I2c2Scl, kTopDarjeelingPinmuxOutselI2c2Scl) \
    value(_, SpiHost1Sd0, kTopDarjeelingPinmuxOutselSpiHost1Sd0) \
    value(_, SpiHost1Sd1, kTopDarjeelingPinmuxOutselSpiHost1Sd1) \
    value(_, SpiHost1Sd2, kTopDarjeelingPinmuxOutselSpiHost1Sd2) \
    value(_, SpiHost1Sd3, kTopDarjeelingPinmuxOutselSpiHost1Sd3) \
    value(_, Uart0Tx, kTopDarjeelingPinmuxOutselUart0Tx) \
    value(_, Uart1Tx, kTopDarjeelingPinmuxOutselUart1Tx) \
    value(_, Uart2Tx, kTopDarjeelingPinmuxOutselUart2Tx) \
    value(_, Uart3Tx, kTopDarjeelingPinmuxOutselUart3Tx) \
    value(_, SpiHost1Sck, kTopDarjeelingPinmuxOutselSpiHost1Sck) \
    value(_, SpiHost1Csb, kTopDarjeelingPinmuxOutselSpiHost1Csb) \
    value(_, FlashCtrlTdo, kTopDarjeelingPinmuxOutselFlashCtrlTdo) \
    value(_, SensorCtrlAstDebugOut0, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut0) \
    value(_, SensorCtrlAstDebugOut1, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut1) \
    value(_, SensorCtrlAstDebugOut2, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut2) \
    value(_, SensorCtrlAstDebugOut3, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut3) \
    value(_, SensorCtrlAstDebugOut4, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut4) \
    value(_, SensorCtrlAstDebugOut5, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut5) \
    value(_, SensorCtrlAstDebugOut6, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut6) \
    value(_, SensorCtrlAstDebugOut7, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut7) \
    value(_, SensorCtrlAstDebugOut8, kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut8) \
    value(_, PwmAonPwm0, kTopDarjeelingPinmuxOutselPwmAonPwm0) \
    value(_, PwmAonPwm1, kTopDarjeelingPinmuxOutselPwmAonPwm1) \
    value(_, PwmAonPwm2, kTopDarjeelingPinmuxOutselPwmAonPwm2) \
    value(_, PwmAonPwm3, kTopDarjeelingPinmuxOutselPwmAonPwm3) \
    value(_, PwmAonPwm4, kTopDarjeelingPinmuxOutselPwmAonPwm4) \
    value(_, PwmAonPwm5, kTopDarjeelingPinmuxOutselPwmAonPwm5) \
    value(_, OtpCtrlTest0, kTopDarjeelingPinmuxOutselOtpCtrlTest0) \
    value(_, SysrstCtrlAonBatDisable, kTopDarjeelingPinmuxOutselSysrstCtrlAonBatDisable) \
    value(_, SysrstCtrlAonKey0Out, kTopDarjeelingPinmuxOutselSysrstCtrlAonKey0Out) \
    value(_, SysrstCtrlAonKey1Out, kTopDarjeelingPinmuxOutselSysrstCtrlAonKey1Out) \
    value(_, SysrstCtrlAonKey2Out, kTopDarjeelingPinmuxOutselSysrstCtrlAonKey2Out) \
    value(_, SysrstCtrlAonPwrbOut, kTopDarjeelingPinmuxOutselSysrstCtrlAonPwrbOut) \
    value(_, SysrstCtrlAonZ3Wakeup, kTopDarjeelingPinmuxOutselSysrstCtrlAonZ3Wakeup) \
    value(_, End, kTopDarjeelingPinmuxOutselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxOutsel, pinmux_outsel_t, TOP_DARJEELING_PINMUX_OUTSEL, WITH_UNKNOWN));

#define TOP_DARJEELING_DIRECT_PADS(_, value) \
    value(_, UsbdevUsbDp, kTopDarjeelingDirectPadsUsbdevUsbDp) \
    value(_, UsbdevUsbDn, kTopDarjeelingDirectPadsUsbdevUsbDn) \
    value(_, SpiHost0Sd0, kTopDarjeelingDirectPadsSpiHost0Sd0) \
    value(_, SpiHost0Sd1, kTopDarjeelingDirectPadsSpiHost0Sd1) \
    value(_, SpiHost0Sd2, kTopDarjeelingDirectPadsSpiHost0Sd2) \
    value(_, SpiHost0Sd3, kTopDarjeelingDirectPadsSpiHost0Sd3) \
    value(_, SpiDeviceSd0, kTopDarjeelingDirectPadsSpiDeviceSd0) \
    value(_, SpiDeviceSd1, kTopDarjeelingDirectPadsSpiDeviceSd1) \
    value(_, SpiDeviceSd2, kTopDarjeelingDirectPadsSpiDeviceSd2) \
    value(_, SpiDeviceSd3, kTopDarjeelingDirectPadsSpiDeviceSd3) \
    value(_, SysrstCtrlAonEcRstL, kTopDarjeelingDirectPadsSysrstCtrlAonEcRstL) \
    value(_, SysrstCtrlAonFlashWpL, kTopDarjeelingDirectPadsSysrstCtrlAonFlashWpL) \
    value(_, SpiDeviceSck, kTopDarjeelingDirectPadsSpiDeviceSck) \
    value(_, SpiDeviceCsb, kTopDarjeelingDirectPadsSpiDeviceCsb) \
    value(_, SpiHost0Sck, kTopDarjeelingDirectPadsSpiHost0Sck) \
    value(_, SpiHost0Csb, kTopDarjeelingDirectPadsSpiHost0Csb) \
    value(_, End, kTopDarjeelingDirectPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(DirectPads, direct_pads_t, TOP_DARJEELING_DIRECT_PADS, WITH_UNKNOWN));

#define TOP_DARJEELING_MUXED_PADS(_, value) \
    value(_, Ioa0, kTopDarjeelingMuxedPadsIoa0) \
    value(_, Ioa1, kTopDarjeelingMuxedPadsIoa1) \
    value(_, Ioa2, kTopDarjeelingMuxedPadsIoa2) \
    value(_, Ioa3, kTopDarjeelingMuxedPadsIoa3) \
    value(_, Ioa4, kTopDarjeelingMuxedPadsIoa4) \
    value(_, Ioa5, kTopDarjeelingMuxedPadsIoa5) \
    value(_, Ioa6, kTopDarjeelingMuxedPadsIoa6) \
    value(_, Ioa7, kTopDarjeelingMuxedPadsIoa7) \
    value(_, Ioa8, kTopDarjeelingMuxedPadsIoa8) \
    value(_, Iob0, kTopDarjeelingMuxedPadsIob0) \
    value(_, Iob1, kTopDarjeelingMuxedPadsIob1) \
    value(_, Iob2, kTopDarjeelingMuxedPadsIob2) \
    value(_, Iob3, kTopDarjeelingMuxedPadsIob3) \
    value(_, Iob4, kTopDarjeelingMuxedPadsIob4) \
    value(_, Iob5, kTopDarjeelingMuxedPadsIob5) \
    value(_, Iob6, kTopDarjeelingMuxedPadsIob6) \
    value(_, Iob7, kTopDarjeelingMuxedPadsIob7) \
    value(_, Iob8, kTopDarjeelingMuxedPadsIob8) \
    value(_, Iob9, kTopDarjeelingMuxedPadsIob9) \
    value(_, Iob10, kTopDarjeelingMuxedPadsIob10) \
    value(_, Iob11, kTopDarjeelingMuxedPadsIob11) \
    value(_, Iob12, kTopDarjeelingMuxedPadsIob12) \
    value(_, Ioc0, kTopDarjeelingMuxedPadsIoc0) \
    value(_, Ioc1, kTopDarjeelingMuxedPadsIoc1) \
    value(_, Ioc2, kTopDarjeelingMuxedPadsIoc2) \
    value(_, Ioc3, kTopDarjeelingMuxedPadsIoc3) \
    value(_, Ioc4, kTopDarjeelingMuxedPadsIoc4) \
    value(_, Ioc5, kTopDarjeelingMuxedPadsIoc5) \
    value(_, Ioc6, kTopDarjeelingMuxedPadsIoc6) \
    value(_, Ioc7, kTopDarjeelingMuxedPadsIoc7) \
    value(_, Ioc8, kTopDarjeelingMuxedPadsIoc8) \
    value(_, Ioc9, kTopDarjeelingMuxedPadsIoc9) \
    value(_, Ioc10, kTopDarjeelingMuxedPadsIoc10) \
    value(_, Ioc11, kTopDarjeelingMuxedPadsIoc11) \
    value(_, Ioc12, kTopDarjeelingMuxedPadsIoc12) \
    value(_, Ior0, kTopDarjeelingMuxedPadsIor0) \
    value(_, Ior1, kTopDarjeelingMuxedPadsIor1) \
    value(_, Ior2, kTopDarjeelingMuxedPadsIor2) \
    value(_, Ior3, kTopDarjeelingMuxedPadsIor3) \
    value(_, Ior4, kTopDarjeelingMuxedPadsIor4) \
    value(_, Ior5, kTopDarjeelingMuxedPadsIor5) \
    value(_, Ior6, kTopDarjeelingMuxedPadsIor6) \
    value(_, Ior7, kTopDarjeelingMuxedPadsIor7) \
    value(_, Ior10, kTopDarjeelingMuxedPadsIor10) \
    value(_, Ior11, kTopDarjeelingMuxedPadsIor11) \
    value(_, Ior12, kTopDarjeelingMuxedPadsIor12) \
    value(_, Ior13, kTopDarjeelingMuxedPadsIor13) \
    value(_, End, kTopDarjeelingMuxedPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(MuxedPads, muxed_pads_t, TOP_DARJEELING_MUXED_PADS, WITH_UNKNOWN));

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
