// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SPI_PASSTHRU_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SPI_PASSTHRU_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define STRUCT_CONFIG_JEDEC_ID(field, string) \
    field(device_id, uint16_t) \
    field(manufacturer_id, uint8_t) \
    field(continuation_code, uint8_t) \
    field(continuation_len, uint8_t)
UJSON_SERDE_STRUCT(ConfigJedecId, config_jedec_id_t, STRUCT_CONFIG_JEDEC_ID);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SPI_PASSTHRU_H_
