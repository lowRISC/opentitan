// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_TEST_WAFER_AUTH_SECRET_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_TEST_WAFER_AUTH_SECRET_H_

#include "sw/device/silicon_creator/manuf/lib/isolated_flash_partition.h"

// Expected wafer authentication secret to write to the flash
const uint32_t kExpectedWaferAuthSecret[kWaferAuthSecretSizeInWords] = {
    0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
    0xdeadbeef, 0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
};

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_TEST_WAFER_AUTH_SECRET_H_
