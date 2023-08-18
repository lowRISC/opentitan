// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/i2c/test/utils/i2c_testutils.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const i2c_pinmux_conf_t kPinmuxConf[] = {
    // I2C0.
    {.sda =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIoa7,
             .insel = kTopEarlgreyPinmuxInselIoa7,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c0Sda,
             .outsel = kTopEarlgreyPinmuxOutselI2c0Sda,
         },
     .scl =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIoa8,
             .insel = kTopEarlgreyPinmuxInselIoa8,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c0Scl,
             .outsel = kTopEarlgreyPinmuxOutselI2c0Scl,
         }},
    // I2C1.
    {.sda =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIob10,
             .insel = kTopEarlgreyPinmuxInselIob10,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c1Sda,
             .outsel = kTopEarlgreyPinmuxOutselI2c1Sda,
         },
     .scl =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIob9,
             .insel = kTopEarlgreyPinmuxInselIob9,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c1Scl,
             .outsel = kTopEarlgreyPinmuxOutselI2c1Scl,
         }},
    // I2C2.
    {.sda =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIob12,
             .insel = kTopEarlgreyPinmuxInselIob12,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c2Sda,
             .outsel = kTopEarlgreyPinmuxOutselI2c2Sda,
         },
     .scl =
         {
             .mio_out = kTopEarlgreyPinmuxMioOutIob11,
             .insel = kTopEarlgreyPinmuxInselIob11,
             .peripheral_in = kTopEarlgreyPinmuxPeripheralInI2c2Scl,
             .outsel = kTopEarlgreyPinmuxOutselI2c2Scl,
         }},
};
