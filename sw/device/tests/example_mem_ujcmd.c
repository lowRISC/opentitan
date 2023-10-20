// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/mem.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

volatile uint8_t kTestBytes[256];
volatile uint32_t kTestWord;
volatile uint32_t kEndTest;

status_t command_processor(ujson_t *uj) {
  while (!kEndTest) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
  return OK_STATUS();
}

bool test_main(void) {
  kEndTest = 0;
  kTestWord = 0xface1234u;
  for (size_t i = 0; i < 256; ++i) {
    kTestBytes[i] = (uint8_t)i;
  }
  ujson_t uj = ujson_ottf_console();

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, command_processor, &uj);
  return status_ok(result);
}
