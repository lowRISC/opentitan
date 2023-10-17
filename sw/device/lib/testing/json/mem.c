// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define UJSON_SERDE_IMPL 1
#include "sw/device/lib/testing/json/mem.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#define MODULE_ID MAKE_MODULE_ID('j', 's', 'm')

status_t ujcmd_mem_read32(ujson_t *uj) {
  mem_read32_req_t op;
  mem_read32_resp_t resp;
  TRY(ujson_deserialize_mem_read32_req_t(uj, &op));
  if ((op.address % sizeof(uint32_t)) != 0) {
    return INVALID_ARGUMENT();
  }
  resp.value = read_32((void *)op.address);
  return RESP_OK(ujson_serialize_mem_read32_resp_t, uj, &resp);
}

status_t ujcmd_mem_read(ujson_t *uj) {
  mem_read_req_t op;
  mem_read_resp_t resp;
  TRY(ujson_deserialize_mem_read_req_t(uj, &op));
  if (op.data_len > sizeof(resp.data)) {
    return INVALID_ARGUMENT();
  }
  memcpy(resp.data, (void *)op.address, op.data_len);
  resp.data_len = op.data_len;
  return RESP_OK(ujson_serialize_mem_read_resp_t, uj, &resp);
}

status_t ujcmd_mem_write32(ujson_t *uj) {
  mem_write32_req_t op;
  TRY(ujson_deserialize_mem_write32_req_t(uj, &op));
  if ((op.address % sizeof(uint32_t)) != 0) {
    return INVALID_ARGUMENT();
  }
  write_32(op.value, (void *)op.address);
  return RESP_OK_STATUS(uj);
}

status_t ujcmd_mem_write(ujson_t *uj) {
  mem_write_req_t op;
  TRY(ujson_deserialize_mem_write_req_t(uj, &op));
  if (op.data_len > sizeof(op.data)) {
    return INVALID_ARGUMENT();
  }
  memcpy((void *)op.address, op.data, op.data_len);
  return RESP_OK_STATUS(uj);
}
