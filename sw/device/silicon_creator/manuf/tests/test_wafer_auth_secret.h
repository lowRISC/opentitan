// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_

#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

// Expected wafer authentication secret to write to the flash
const uint32_t
    kExpectedWaferAuthSecret[kFlashInfoWaferAuthSecretSizeIn32BitWords] = {
        0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
        0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_TESTS_TEST_WAFER_AUTH_SECRET_H_
