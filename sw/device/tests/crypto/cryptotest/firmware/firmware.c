// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <stdbool.h>

#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/lib/crypto_test_lib.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Include commands
#include "sw/device/tests/crypto/cryptotest/json/aes_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/aes_gcm_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/commands.h"
#include "sw/device/tests/crypto/cryptotest/json/drbg_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdh_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ecdsa_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/ed25519_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/hash_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/hmac_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/kmac_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/rsa_commands.h"
#include "sw/device/tests/crypto/cryptotest/json/sphincsplus_commands.h"

// Include handlers
#include "aes.h"
#include "aes_gcm.h"
#include "drbg.h"
#include "ecdh.h"
#include "ecdsa.h"
#include "ed25519.h"
#include "hash.h"
#include "hmac.h"
#include "kmac.h"
#include "rsa.h"
#include "sphincsplus.h"

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false, );

status_t process_cmd(ujson_t *uj) {
  while (true) {
    cryptotest_cmd_t cmd;
    TRY(ujson_deserialize_cryptotest_cmd_t(uj, &cmd));
    switch (cmd) {
      case kCryptotestCommandAes:
        RESP_ERR(uj, handle_aes(uj));
        break;
      case kCryptotestCommandAesGcm:
        RESP_ERR(uj, handle_aes_gcm(uj));
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
      case kCryptotestCommandEd25519:
        RESP_ERR(uj, handle_ed25519(uj));
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
      case kCryptotestCommandQuit:
        return OK_STATUS(0);
      case kCryptotestCommandRsa:
        RESP_ERR(uj, handle_rsa(uj));
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
  // We pick a random security level for the entire test run
  otcrypto_key_security_level_t sec_level;
  CHECK_STATUS_OK(determine_security_level(&sec_level));
#ifdef OT_COVERAGE_INSTRUMENTED
  // Coverage becomes flaky with the jittery clock and dummy operations.
  sec_level = kOtcryptoKeySecurityLevelLow;
#endif
  CHECK_STATUS_OK(otcrypto_init(sec_level));
  ujson_t uj = ujson_ottf_console();
  return status_ok(process_cmd(&uj));
}
