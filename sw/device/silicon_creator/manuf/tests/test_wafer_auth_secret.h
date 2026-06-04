// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_

#include "sw/device/silicon_creator/manuf/lib/nvm_info_field.h"

// Expected wafer authentication secret to write to the NVM
const uint32_t
    kExpectedWaferAuthSecret[kNvmInfoFieldWaferAuthSecretSizeIn32BitWords] = {
        0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
        0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_
