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
    value(_, SocGpi12, kTopDarjeelingPinmuxPeripheralInSocProxySocGpi12) \
    value(_, SocGpi13, kTopDarjeelingPinmuxPeripheralInSocProxySocGpi13) \
    value(_, SocGpi14, kTopDarjeelingPinmuxPeripheralInSocProxySocGpi14) \
    value(_, SocGpi15, kTopDarjeelingPinmuxPeripheralInSocProxySocGpi15) \
    value(_, End, kTopDarjeelingPinmuxPeripheralInLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxPeripheralIn, pinmux_peripheral_in_t, TOP_DARJEELING_PINMUX_PERIPHERAL_IN, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_INSEL(_, value) \
    value(_, ConstantZero, kTopDarjeelingPinmuxInselConstantZero) \
    value(_, ConstantOne, kTopDarjeelingPinmuxInselConstantOne) \
    value(_, Mio0, kTopDarjeelingPinmuxInselMio0) \
    value(_, Mio1, kTopDarjeelingPinmuxInselMio1) \
    value(_, Mio2, kTopDarjeelingPinmuxInselMio2) \
    value(_, Mio3, kTopDarjeelingPinmuxInselMio3) \
    value(_, Mio4, kTopDarjeelingPinmuxInselMio4) \
    value(_, Mio5, kTopDarjeelingPinmuxInselMio5) \
    value(_, Mio6, kTopDarjeelingPinmuxInselMio6) \
    value(_, Mio7, kTopDarjeelingPinmuxInselMio7) \
    value(_, Mio8, kTopDarjeelingPinmuxInselMio8) \
    value(_, Mio9, kTopDarjeelingPinmuxInselMio9) \
    value(_, Mio10, kTopDarjeelingPinmuxInselMio10) \
    value(_, Mio11, kTopDarjeelingPinmuxInselMio11) \
    value(_, End, kTopDarjeelingPinmuxInselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxInsel, pinmux_insel_t, TOP_DARJEELING_PINMUX_INSEL, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_MIO_OUT(_, value) \
    value(_, Mio0, kTopDarjeelingPinmuxMioOutMio0) \
    value(_, Mio1, kTopDarjeelingPinmuxMioOutMio1) \
    value(_, Mio2, kTopDarjeelingPinmuxMioOutMio2) \
    value(_, Mio3, kTopDarjeelingPinmuxMioOutMio3) \
    value(_, Mio4, kTopDarjeelingPinmuxMioOutMio4) \
    value(_, Mio5, kTopDarjeelingPinmuxMioOutMio5) \
    value(_, Mio6, kTopDarjeelingPinmuxMioOutMio6) \
    value(_, Mio7, kTopDarjeelingPinmuxMioOutMio7) \
    value(_, Mio8, kTopDarjeelingPinmuxMioOutMio8) \
    value(_, Mio9, kTopDarjeelingPinmuxMioOutMio9) \
    value(_, Mio10, kTopDarjeelingPinmuxMioOutMio10) \
    value(_, Mio11, kTopDarjeelingPinmuxMioOutMio11) \
    value(_, End, kTopDarjeelingPinmuxMioOutLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxMioOut, pinmux_mio_out_t, TOP_DARJEELING_PINMUX_MIO_OUT, WITH_UNKNOWN));

#define TOP_DARJEELING_PINMUX_OUTSEL(_, value) \
    value(_, ConstantZero, kTopDarjeelingPinmuxOutselConstantZero) \
    value(_, ConstantOne, kTopDarjeelingPinmuxOutselConstantOne) \
    value(_, ConstantHighZ, kTopDarjeelingPinmuxOutselConstantHighZ) \
    value(_, SocProxySocGpo12, kTopDarjeelingPinmuxOutselSocProxySocGpo12) \
    value(_, SocProxySocGpo13, kTopDarjeelingPinmuxOutselSocProxySocGpo13) \
    value(_, SocProxySocGpo14, kTopDarjeelingPinmuxOutselSocProxySocGpo14) \
    value(_, SocProxySocGpo15, kTopDarjeelingPinmuxOutselSocProxySocGpo15) \
    value(_, OtpCtrlTest0, kTopDarjeelingPinmuxOutselOtpCtrlTest0) \
    value(_, End, kTopDarjeelingPinmuxOutselLast + 1)
C_ONLY(UJSON_SERDE_ENUM(PinmuxOutsel, pinmux_outsel_t, TOP_DARJEELING_PINMUX_OUTSEL, WITH_UNKNOWN));

#define TOP_DARJEELING_DIRECT_PADS(_, value) \
    value(_, SpiHost0Sd0, kTopDarjeelingDirectPadsSpiHost0Sd0) \
    value(_, SpiHost0Sd1, kTopDarjeelingDirectPadsSpiHost0Sd1) \
    value(_, SpiHost0Sd2, kTopDarjeelingDirectPadsSpiHost0Sd2) \
    value(_, SpiHost0Sd3, kTopDarjeelingDirectPadsSpiHost0Sd3) \
    value(_, SpiDeviceSd0, kTopDarjeelingDirectPadsSpiDeviceSd0) \
    value(_, SpiDeviceSd1, kTopDarjeelingDirectPadsSpiDeviceSd1) \
    value(_, SpiDeviceSd2, kTopDarjeelingDirectPadsSpiDeviceSd2) \
    value(_, SpiDeviceSd3, kTopDarjeelingDirectPadsSpiDeviceSd3) \
    value(_, I2c0Scl, kTopDarjeelingDirectPadsI2c0Scl) \
    value(_, I2c0Sda, kTopDarjeelingDirectPadsI2c0Sda) \
    value(_, GpioGpio0, kTopDarjeelingDirectPadsGpioGpio0) \
    value(_, GpioGpio1, kTopDarjeelingDirectPadsGpioGpio1) \
    value(_, GpioGpio2, kTopDarjeelingDirectPadsGpioGpio2) \
    value(_, GpioGpio3, kTopDarjeelingDirectPadsGpioGpio3) \
    value(_, GpioGpio4, kTopDarjeelingDirectPadsGpioGpio4) \
    value(_, GpioGpio5, kTopDarjeelingDirectPadsGpioGpio5) \
    value(_, GpioGpio6, kTopDarjeelingDirectPadsGpioGpio6) \
    value(_, GpioGpio7, kTopDarjeelingDirectPadsGpioGpio7) \
    value(_, GpioGpio8, kTopDarjeelingDirectPadsGpioGpio8) \
    value(_, GpioGpio9, kTopDarjeelingDirectPadsGpioGpio9) \
    value(_, GpioGpio10, kTopDarjeelingDirectPadsGpioGpio10) \
    value(_, GpioGpio11, kTopDarjeelingDirectPadsGpioGpio11) \
    value(_, GpioGpio12, kTopDarjeelingDirectPadsGpioGpio12) \
    value(_, GpioGpio13, kTopDarjeelingDirectPadsGpioGpio13) \
    value(_, GpioGpio14, kTopDarjeelingDirectPadsGpioGpio14) \
    value(_, GpioGpio15, kTopDarjeelingDirectPadsGpioGpio15) \
    value(_, GpioGpio16, kTopDarjeelingDirectPadsGpioGpio16) \
    value(_, GpioGpio17, kTopDarjeelingDirectPadsGpioGpio17) \
    value(_, GpioGpio18, kTopDarjeelingDirectPadsGpioGpio18) \
    value(_, GpioGpio19, kTopDarjeelingDirectPadsGpioGpio19) \
    value(_, GpioGpio20, kTopDarjeelingDirectPadsGpioGpio20) \
    value(_, GpioGpio21, kTopDarjeelingDirectPadsGpioGpio21) \
    value(_, GpioGpio22, kTopDarjeelingDirectPadsGpioGpio22) \
    value(_, GpioGpio23, kTopDarjeelingDirectPadsGpioGpio23) \
    value(_, GpioGpio24, kTopDarjeelingDirectPadsGpioGpio24) \
    value(_, GpioGpio25, kTopDarjeelingDirectPadsGpioGpio25) \
    value(_, GpioGpio26, kTopDarjeelingDirectPadsGpioGpio26) \
    value(_, GpioGpio27, kTopDarjeelingDirectPadsGpioGpio27) \
    value(_, GpioGpio28, kTopDarjeelingDirectPadsGpioGpio28) \
    value(_, GpioGpio29, kTopDarjeelingDirectPadsGpioGpio29) \
    value(_, GpioGpio30, kTopDarjeelingDirectPadsGpioGpio30) \
    value(_, GpioGpio31, kTopDarjeelingDirectPadsGpioGpio31) \
    value(_, SpiDeviceSck, kTopDarjeelingDirectPadsSpiDeviceSck) \
    value(_, SpiDeviceCsb, kTopDarjeelingDirectPadsSpiDeviceCsb) \
    value(_, SpiDeviceTpmCsb, kTopDarjeelingDirectPadsSpiDeviceTpmCsb) \
    value(_, Uart0Rx, kTopDarjeelingDirectPadsUart0Rx) \
    value(_, SocProxySocGpi0, kTopDarjeelingDirectPadsSocProxySocGpi0) \
    value(_, SocProxySocGpi1, kTopDarjeelingDirectPadsSocProxySocGpi1) \
    value(_, SocProxySocGpi2, kTopDarjeelingDirectPadsSocProxySocGpi2) \
    value(_, SocProxySocGpi3, kTopDarjeelingDirectPadsSocProxySocGpi3) \
    value(_, SocProxySocGpi4, kTopDarjeelingDirectPadsSocProxySocGpi4) \
    value(_, SocProxySocGpi5, kTopDarjeelingDirectPadsSocProxySocGpi5) \
    value(_, SocProxySocGpi6, kTopDarjeelingDirectPadsSocProxySocGpi6) \
    value(_, SocProxySocGpi7, kTopDarjeelingDirectPadsSocProxySocGpi7) \
    value(_, SocProxySocGpi8, kTopDarjeelingDirectPadsSocProxySocGpi8) \
    value(_, SocProxySocGpi9, kTopDarjeelingDirectPadsSocProxySocGpi9) \
    value(_, SocProxySocGpi10, kTopDarjeelingDirectPadsSocProxySocGpi10) \
    value(_, SocProxySocGpi11, kTopDarjeelingDirectPadsSocProxySocGpi11) \
    value(_, SpiHost0Sck, kTopDarjeelingDirectPadsSpiHost0Sck) \
    value(_, SpiHost0Csb, kTopDarjeelingDirectPadsSpiHost0Csb) \
    value(_, Uart0Tx, kTopDarjeelingDirectPadsUart0Tx) \
    value(_, SocProxySocGpo0, kTopDarjeelingDirectPadsSocProxySocGpo0) \
    value(_, SocProxySocGpo1, kTopDarjeelingDirectPadsSocProxySocGpo1) \
    value(_, SocProxySocGpo2, kTopDarjeelingDirectPadsSocProxySocGpo2) \
    value(_, SocProxySocGpo3, kTopDarjeelingDirectPadsSocProxySocGpo3) \
    value(_, SocProxySocGpo4, kTopDarjeelingDirectPadsSocProxySocGpo4) \
    value(_, SocProxySocGpo5, kTopDarjeelingDirectPadsSocProxySocGpo5) \
    value(_, SocProxySocGpo6, kTopDarjeelingDirectPadsSocProxySocGpo6) \
    value(_, SocProxySocGpo7, kTopDarjeelingDirectPadsSocProxySocGpo7) \
    value(_, SocProxySocGpo8, kTopDarjeelingDirectPadsSocProxySocGpo8) \
    value(_, SocProxySocGpo9, kTopDarjeelingDirectPadsSocProxySocGpo9) \
    value(_, SocProxySocGpo10, kTopDarjeelingDirectPadsSocProxySocGpo10) \
    value(_, SocProxySocGpo11, kTopDarjeelingDirectPadsSocProxySocGpo11) \
    value(_, End, kTopDarjeelingDirectPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(DirectPads, direct_pads_t, TOP_DARJEELING_DIRECT_PADS, WITH_UNKNOWN));

#define TOP_DARJEELING_MUXED_PADS(_, value) \
    value(_, Mio0, kTopDarjeelingMuxedPadsMio0) \
    value(_, Mio1, kTopDarjeelingMuxedPadsMio1) \
    value(_, Mio2, kTopDarjeelingMuxedPadsMio2) \
    value(_, Mio3, kTopDarjeelingMuxedPadsMio3) \
    value(_, Mio4, kTopDarjeelingMuxedPadsMio4) \
    value(_, Mio5, kTopDarjeelingMuxedPadsMio5) \
    value(_, Mio6, kTopDarjeelingMuxedPadsMio6) \
    value(_, Mio7, kTopDarjeelingMuxedPadsMio7) \
    value(_, Mio8, kTopDarjeelingMuxedPadsMio8) \
    value(_, Mio9, kTopDarjeelingMuxedPadsMio9) \
    value(_, Mio10, kTopDarjeelingMuxedPadsMio10) \
    value(_, Mio11, kTopDarjeelingMuxedPadsMio11) \
    value(_, End, kTopDarjeelingMuxedPadsLast + 1)
C_ONLY(UJSON_SERDE_ENUM(MuxedPads, muxed_pads_t, TOP_DARJEELING_MUXED_PADS, WITH_UNKNOWN));

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_PINMUX_H_
