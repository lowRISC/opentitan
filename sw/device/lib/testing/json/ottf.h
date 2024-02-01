// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_OTTF_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_OTTF_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define MODULE_ID MAKE_MODULE_ID('j', 'o', 't')

#define STRUCT_OTTF_CRC(field, string) \
    field(crc, uint32_t)
UJSON_SERDE_STRUCT(OttfCrc, ottf_crc_t, STRUCT_OTTF_CRC);

#undef MODULE_ID

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_OTTF_H_
