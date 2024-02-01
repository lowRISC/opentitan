// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "sw/device/lib/base/bitfield.h"

#define HW_CFG1_EN_OFFSET(m, i) ((bitfield_field32_t){.mask = m, .index = i})
const bitfield_field32_t kSramFetch = HW_CFG1_EN_OFFSET(0xff, 0);
const bitfield_field32_t kCsrngAppRead = HW_CFG1_EN_OFFSET(0xff, 8);
const bitfield_field32_t kDisRvDmLateDebug = HW_CFG1_EN_OFFSET(0xff, 16);
#undef HW_CFG1_EN_OFFSET
