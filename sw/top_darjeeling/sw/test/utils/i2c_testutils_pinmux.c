// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/i2c/test/utils/i2c_testutils.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

const i2c_pinmux_conf_t kPinmuxConf[] = {
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
};
