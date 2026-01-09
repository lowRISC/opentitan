// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/base/cp_device_id.h"

/**
 * CP (SKU specific portion of) device ID.
 */
const uint32_t kCpDeviceId[4] = {${device_id}};
