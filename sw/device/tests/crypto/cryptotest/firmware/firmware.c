// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

// Include commands
#include "sw/device/tests/crypto/cryptotest/json/aes_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/commands.h"
#include "sw/device/tests/crypto/cryptotest/json/drbg_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdh_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/hash_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/hmac_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/kmac_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/sphincsplus_commands.h"

// Include handlers
#include "aes.h"
#include "drbg.h"
#include "ecdh.h"
#include "ecdsa.h"
#include "hash.h"
#include "hmac.h"
#include "kmac.h"
#include "sphincsplus.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

status_t process_cmd(ujson_t *uj) {
  while (true) {
    cryptotest_cmd_t cmd;
    TRY(ujson_deserialize_cryptotest_cmd_t(uj, &cmd));
    switch (cmd) {
      case kCryptotestCommandAes:
        RESP_ERR(uj, handle_aes(uj));
        break;
      case kCryptotestCommandDrbg:
        RESP_ERR(uj, handle_drbg(uj));
        break;
      case kCryptotestCommandEcdsa:
        RESP_ERR(uj, handle_ecdsa(uj));
        break;
      case kCryptotestCommandEcdh:
        RESP_ERR(uj, handle_ecdh(uj));
        break;
      case kCryptotestCommandHash:
        RESP_ERR(uj, handle_hash(uj));
        break;
      case kCryptotestCommandHmac:
        RESP_ERR(uj, handle_hmac(uj));
        break;
      case kCryptotestCommandKmac:
        RESP_ERR(uj, handle_kmac(uj));
        break;
      case kCryptotestCommandSphincsPlus:
        RESP_ERR(uj, handle_sphincsplus(uj));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", cmd);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }

  return OK_STATUS(0);
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_complex_init());
  ujson_t uj = ujson_ottf_console();
  return status_ok(process_cmd(&uj));
}
