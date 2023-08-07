// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/i2c/test/utils/i2c_testutils.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"


const i2c_pinmux_conf_t pinmux_conf[] = {
    // I2C0.
    {.sda =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIoa7,
             .insel = kTopDarjeelingPinmuxInselIoa7,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c0Sda,
             .outsel = kTopDarjeelingPinmuxOutselI2c0Sda,
         },
     .scl =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIoa8,
             .insel = kTopDarjeelingPinmuxInselIoa8,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c0Scl,
             .outsel = kTopDarjeelingPinmuxOutselI2c0Scl,
         }},
    // I2C1.
    {.sda =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIob10,
             .insel = kTopDarjeelingPinmuxInselIob10,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c1Sda,
             .outsel = kTopDarjeelingPinmuxOutselI2c1Sda,
         },
     .scl =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIob9,
             .insel = kTopDarjeelingPinmuxInselIob9,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c1Scl,
             .outsel = kTopDarjeelingPinmuxOutselI2c1Scl,
         }},
    // I2C2.
    {.sda =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIob12,
             .insel = kTopDarjeelingPinmuxInselIob12,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c2Sda,
             .outsel = kTopDarjeelingPinmuxOutselI2c2Sda,
         },
     .scl =
         {
             .mio_out = kTopDarjeelingPinmuxMioOutIob11,
             .insel = kTopDarjeelingPinmuxInselIob11,
             .peripheral_in = kTopDarjeelingPinmuxPeripheralInI2c2Scl,
             .outsel = kTopDarjeelingPinmuxOutselI2c2Scl,
         }},
};
