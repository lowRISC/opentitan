// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/manuf/lib/otp_fields.h"

#include "sw/device/lib/base/bitfield.h"

#define HW_CFG_EN_OFFSET(m, i) ((bitfield_field32_t){.mask = m, .index = i})
const bitfield_field32_t kSramFetch = HW_CFG_EN_OFFSET(0xff, 0);
const bitfield_field32_t kCsrngAppRead = HW_CFG_EN_OFFSET(0xff, 8);
const bitfield_field32_t kEntropySrcFwRd = HW_CFG_EN_OFFSET(0xff, 16);
const bitfield_field32_t kEntropySrcFwOvr = HW_CFG_EN_OFFSET(0xff, 24);
#undef HW_CFG_EN_OFFSET
