// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/json/mem.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Tests SPI device integration with the ujson OTTF console.
 *
 * This test verifies the ability to send and receive personalized
 * blob ujson structs and mem commands/payloads between the host
 * and the SPI device using the OTTF console.
 */

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

volatile uint8_t kTestBytes[256];
volatile uint32_t kTestWord;
volatile uint32_t kEndTest;
static perso_blob_t perso_blob_to_host;
static perso_blob_t perso_blob_from_host;

status_t command_processor(ujson_t *uj) {
  while (!kEndTest) {
    test_command_t command;
    TRY(UJSON_WITH_CRC(ujson_deserialize_test_command_t, uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
  return OK_STATUS();
}

status_t perso_blob_transaction_test(ujson_t *uj) {
  LOG_INFO("SYNC: Sending perso blob");
  TRY(RESP_OK(ujson_serialize_perso_blob_t, uj, &perso_blob_to_host));
  memset(&perso_blob_from_host, 0xa5, sizeof(perso_blob_from_host));
  LOG_INFO("SYNC: Waiting for perso blob");
  TRY(ujson_deserialize_perso_blob_t(uj, &perso_blob_from_host));
  CHECK_ARRAYS_EQ((uint8_t *)&perso_blob_to_host,
                  (uint8_t *)&perso_blob_from_host,
                  sizeof(perso_blob_from_host));
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
  EXECUTE_TEST(result, perso_blob_transaction_test, &uj);
  EXECUTE_TEST(result, command_processor, &uj);

  return status_ok(result);
}
