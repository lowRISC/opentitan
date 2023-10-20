// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"

#include "sw/device/lib/testing/json/mem.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

status_t ujson_ottf_dispatch(ujson_t *uj, test_command_t command) {
  if (uj == NULL) {
    return INVALID_ARGUMENT();
  }
  switch (command) {
    case kTestCommandMemRead32:
      RESP_ERR(uj, ujcmd_mem_read32(uj));
      break;
    case kTestCommandMemRead:
      RESP_ERR(uj, ujcmd_mem_read(uj));
      break;
    case kTestCommandMemWrite32:
      RESP_ERR(uj, ujcmd_mem_write32(uj));
      break;
    case kTestCommandMemWrite:
      RESP_ERR(uj, ujcmd_mem_write(uj));
      break;
    default:
      return UNIMPLEMENTED();
  }
  return OK_STATUS();
}
