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

#define STRUCT_STATUS_REGISTER(field, string) \
    field(status, uint32_t) \
    field(addr_4b, bool)
UJSON_SERDE_STRUCT(StatusRegister, status_register_t, STRUCT_STATUS_REGISTER);

#define STRUCT_SFDP_DATA(field, string) \
    field(data, uint8_t, 256)
UJSON_SERDE_STRUCT(SfdpData, sfdp_data_t, STRUCT_SFDP_DATA);

#define STRUCT_UPLOAD_INFO(field, string) \
    field(opcode, uint8_t) \
    field(has_address, bool) \
    field(addr_4b, bool) \
    field(data_len, uint16_t) \
    field(flash_status, uint32_t) \
    field(address, uint32_t) \
    field(data, uint8_t, 256)
UJSON_SERDE_STRUCT(UploadInfo, upload_info_t, STRUCT_UPLOAD_INFO);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_SPI_PASSTHRU_H_
