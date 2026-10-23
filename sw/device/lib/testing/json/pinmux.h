// Copyright lowRISC contributors (OpenTitan project).
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
    value(_, Gpio0Gpio0, kTopEarlgreyPinmuxPeripheralInGpio0Gpio0) \
    value(_, Gpio0Gpio1, kTopEarlgreyPinmuxPeripheralInGpio0Gpio1) \
    value(_, Gpio0Gpio2, kTopEarlgreyPinmuxPeripheralInGpio0Gpio2) \
    value(_, Gpio0Gpio3, kTopEarlgreyPinmuxPeripheralInGpio0Gpio3) \
    value(_, Gpio0Gpio4, kTopEarlgreyPinmuxPeripheralInGpio0Gpio4) \
    value(_, Gpio0Gpio5, kTopEarlgreyPinmuxPeripheralInGpio0Gpio5) \
    value(_, Gpio0Gpio6, kTopEarlgreyPinmuxPeripheralInGpio0Gpio6) \
    value(_, Gpio0Gpio7, kTopEarlgreyPinmuxPeripheralInGpio0Gpio7) \
    value(_, Gpio0Gpio8, kTopEarlgreyPinmuxPeripheralInGpio0Gpio8) \
    value(_, Gpio0Gpio9, kTopEarlgreyPinmuxPeripheralInGpio0Gpio9) \
    value(_, Gpio0Gpio10, kTopEarlgreyPinmuxPeripheralInGpio0Gpio10) \
    value(_, Gpio0Gpio11, kTopEarlgreyPinmuxPeripheralInGpio0Gpio11) \
    value(_, Gpio0Gpio12, kTopEarlgreyPinmuxPeripheralInGpio0Gpio12) \
    value(_, Gpio0Gpio13, kTopEarlgreyPinmuxPeripheralInGpio0Gpio13) \
    value(_, Gpio0Gpio14, kTopEarlgreyPinmuxPeripheralInGpio0Gpio14) \
    value(_, Gpio0Gpio15, kTopEarlgreyPinmuxPeripheralInGpio0Gpio15) \
    value(_, Gpio0Gpio16, kTopEarlgreyPinmuxPeripheralInGpio0Gpio16) \
    value(_, Gpio0Gpio17, kTopEarlgreyPinmuxPeripheralInGpio0Gpio17) \
    value(_, Gpio0Gpio18, kTopEarlgreyPinmuxPeripheralInGpio0Gpio18) \
    value(_, Gpio0Gpio19, kTopEarlgreyPinmuxPeripheralInGpio0Gpio19) \
    value(_, Gpio0Gpio20, kTopEarlgreyPinmuxPeripheralInGpio0Gpio20) \
    value(_, Gpio0Gpio21, kTopEarlgreyPinmuxPeripheralInGpio0Gpio21) \
    value(_, Gpio0Gpio22, kTopEarlgreyPinmuxPeripheralInGpio0Gpio22) \
    value(_, Gpio0Gpio23, kTopEarlgreyPinmuxPeripheralInGpio0Gpio23) \
    value(_, Gpio0Gpio24, kTopEarlgreyPinmuxPeripheralInGpio0Gpio24) \
    value(_, Gpio0Gpio25, kTopEarlgreyPinmuxPeripheralInGpio0Gpio25) \
    value(_, Gpio0Gpio26, kTopEarlgreyPinmuxPeripheralInGpio0Gpio26) \
    value(_, Gpio0Gpio27, kTopEarlgreyPinmuxPeripheralInGpio0Gpio27) \
    value(_, Gpio0Gpio28, kTopEarlgreyPinmuxPeripheralInGpio0Gpio28) \
    value(_, Gpio0Gpio29, kTopEarlgreyPinmuxPeripheralInGpio0Gpio29) \
    value(_, Gpio0Gpio30, kTopEarlgreyPinmuxPeripheralInGpio0Gpio30) \
    value(_, Gpio0Gpio31, kTopEarlgreyPinmuxPeripheralInGpio0Gpio31) \
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
    value(_, RramMacroTck, kTopEarlgreyPinmuxPeripheralInRramMacroTck) \
    value(_, RramMacroTms, kTopEarlgreyPinmuxPeripheralInRramMacroTms) \
    value(_, RramMacroTdi, kTopEarlgreyPinmuxPeripheralInRramMacroTdi) \
    value(_, SysrstCtrlAcPresent, kTopEarlgreyPinmuxPeripheralInSysrstCtrlAcPresent) \
    value(_, SysrstCtrlKey0In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey0In) \
    value(_, SysrstCtrlKey1In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey1In) \
    value(_, SysrstCtrlKey2In, kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey2In) \
    value(_, SysrstCtrlPwrbIn, kTopEarlgreyPinmuxPeripheralInSysrstCtrlPwrbIn) \
    value(_, SysrstCtrlLidOpen, kTopEarlgreyPinmuxPeripheralInSysrstCtrlLidOpen) \
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
    value(_, Gpio0Gpio0, kTopEarlgreyPinmuxOutselGpio0Gpio0) \
    value(_, Gpio0Gpio1, kTopEarlgreyPinmuxOutselGpio0Gpio1) \
    value(_, Gpio0Gpio2, kTopEarlgreyPinmuxOutselGpio0Gpio2) \
    value(_, Gpio0Gpio3, kTopEarlgreyPinmuxOutselGpio0Gpio3) \
    value(_, Gpio0Gpio4, kTopEarlgreyPinmuxOutselGpio0Gpio4) \
    value(_, Gpio0Gpio5, kTopEarlgreyPinmuxOutselGpio0Gpio5) \
    value(_, Gpio0Gpio6, kTopEarlgreyPinmuxOutselGpio0Gpio6) \
    value(_, Gpio0Gpio7, kTopEarlgreyPinmuxOutselGpio0Gpio7) \
    value(_, Gpio0Gpio8, kTopEarlgreyPinmuxOutselGpio0Gpio8) \
    value(_, Gpio0Gpio9, kTopEarlgreyPinmuxOutselGpio0Gpio9) \
    value(_, Gpio0Gpio10, kTopEarlgreyPinmuxOutselGpio0Gpio10) \
    value(_, Gpio0Gpio11, kTopEarlgreyPinmuxOutselGpio0Gpio11) \
    value(_, Gpio0Gpio12, kTopEarlgreyPinmuxOutselGpio0Gpio12) \
    value(_, Gpio0Gpio13, kTopEarlgreyPinmuxOutselGpio0Gpio13) \
    value(_, Gpio0Gpio14, kTopEarlgreyPinmuxOutselGpio0Gpio14) \
    value(_, Gpio0Gpio15, kTopEarlgreyPinmuxOutselGpio0Gpio15) \
    value(_, Gpio0Gpio16, kTopEarlgreyPinmuxOutselGpio0Gpio16) \
    value(_, Gpio0Gpio17, kTopEarlgreyPinmuxOutselGpio0Gpio17) \
    value(_, Gpio0Gpio18, kTopEarlgreyPinmuxOutselGpio0Gpio18) \
    value(_, Gpio0Gpio19, kTopEarlgreyPinmuxOutselGpio0Gpio19) \
    value(_, Gpio0Gpio20, kTopEarlgreyPinmuxOutselGpio0Gpio20) \
    value(_, Gpio0Gpio21, kTopEarlgreyPinmuxOutselGpio0Gpio21) \
    value(_, Gpio0Gpio22, kTopEarlgreyPinmuxOutselGpio0Gpio22) \
    value(_, Gpio0Gpio23, kTopEarlgreyPinmuxOutselGpio0Gpio23) \
    value(_, Gpio0Gpio24, kTopEarlgreyPinmuxOutselGpio0Gpio24) \
    value(_, Gpio0Gpio25, kTopEarlgreyPinmuxOutselGpio0Gpio25) \
    value(_, Gpio0Gpio26, kTopEarlgreyPinmuxOutselGpio0Gpio26) \
    value(_, Gpio0Gpio27, kTopEarlgreyPinmuxOutselGpio0Gpio27) \
    value(_, Gpio0Gpio28, kTopEarlgreyPinmuxOutselGpio0Gpio28) \
    value(_, Gpio0Gpio29, kTopEarlgreyPinmuxOutselGpio0Gpio29) \
    value(_, Gpio0Gpio30, kTopEarlgreyPinmuxOutselGpio0Gpio30) \
    value(_, Gpio0Gpio31, kTopEarlgreyPinmuxOutselGpio0Gpio31) \
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
    value(_, SpiHost1Sck, kTopEarlgreyPinmuxOutselSpiHost1Sck) \
    value(_, SpiHost1Csb, kTopEarlgreyPinmuxOutselSpiHost1Csb) \
    value(_, RramMacroTdo, kTopEarlgreyPinmuxOutselRramMacroTdo) \
    value(_, SensorCtrlAstDebugOut0, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut0) \
    value(_, SensorCtrlAstDebugOut1, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut1) \
    value(_, SensorCtrlAstDebugOut2, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut2) \
    value(_, SensorCtrlAstDebugOut3, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut3) \
    value(_, SensorCtrlAstDebugOut4, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut4) \
    value(_, SensorCtrlAstDebugOut5, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut5) \
    value(_, SensorCtrlAstDebugOut6, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut6) \
    value(_, SensorCtrlAstDebugOut7, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut7) \
    value(_, SensorCtrlAstDebugOut8, kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut8) \
    value(_, SysrstCtrlBatDisable, kTopEarlgreyPinmuxOutselSysrstCtrlBatDisable) \
    value(_, SysrstCtrlKey0Out, kTopEarlgreyPinmuxOutselSysrstCtrlKey0Out) \
    value(_, SysrstCtrlKey1Out, kTopEarlgreyPinmuxOutselSysrstCtrlKey1Out) \
    value(_, SysrstCtrlKey2Out, kTopEarlgreyPinmuxOutselSysrstCtrlKey2Out) \
    value(_, SysrstCtrlPwrbOut, kTopEarlgreyPinmuxOutselSysrstCtrlPwrbOut) \
    value(_, SysrstCtrlZ3Wakeup, kTopEarlgreyPinmuxOutselSysrstCtrlZ3Wakeup) \
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
    value(_, SysrstCtrlEcRstL, kTopEarlgreyDirectPadsSysrstCtrlEcRstL) \
    value(_, SysrstCtrlFlashWpL, kTopEarlgreyDirectPadsSysrstCtrlFlashWpL) \
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
