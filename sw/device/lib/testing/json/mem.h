// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_MEM_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_MEM_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define MODULE_ID MAKE_MODULE_ID('j', 'm', 'h')

#define STRUCT_MEM_READ32_REQ(field, string) \
    field(address, uint32_t)
UJSON_SERDE_STRUCT(MemRead32Req, mem_read32_req_t, STRUCT_MEM_READ32_REQ);

#define STRUCT_MEM_READ32_RESP(field, string) \
    field(value, uint32_t)
UJSON_SERDE_STRUCT(MemRead32Resp, mem_read32_resp_t, STRUCT_MEM_READ32_RESP);

#define STRUCT_MEM_READ_REQ(field, string) \
    field(address, uint32_t) \
    field(data_len, uint16_t)
UJSON_SERDE_STRUCT(MemReadReq, mem_read_req_t, STRUCT_MEM_READ_REQ);

#define STRUCT_MEM_READ_RESP(field, string) \
    field(data, uint8_t, 256) \
    field(data_len, uint16_t)
UJSON_SERDE_STRUCT(MemReadResp, mem_read_resp_t, STRUCT_MEM_READ_RESP);

#define STRUCT_MEM_WRITE32_REQ(field, string) \
    field(address, uint32_t) \
    field(value, uint32_t)
UJSON_SERDE_STRUCT(MemWrite32Req, mem_write32_req_t, STRUCT_MEM_WRITE32_REQ);

#define STRUCT_MEM_WRITE_REQ(field, string) \
    field(address, uint32_t) \
    field(data, uint8_t, 256) \
    field(data_len, uint16_t)
UJSON_SERDE_STRUCT(MemWriteReq, mem_write_req_t, STRUCT_MEM_WRITE_REQ);

#ifndef RUST_PREPROCESSOR_EMIT

status_t ujcmd_mem_read32(ujson_t *uj);
status_t ujcmd_mem_read(ujson_t *uj);
status_t ujcmd_mem_write32(ujson_t *uj);
status_t ujcmd_mem_write(ujson_t *uj);

#endif

#undef MODULE_ID

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_MEM_H_
