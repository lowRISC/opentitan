// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_debugger.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"

static status_t _ottf_debugger_loop(ujson_t *uj) {
  LOG_INFO("Debugger started");
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
}

status_t ottf_debugger_loop(ujson_t *ujson) {
  if (ujson == NULL) {
    ujson_t uj = ujson_ottf_console();
    return _ottf_debugger_loop(&uj);
  } else {
    return _ottf_debugger_loop(ujson);
  }
}
