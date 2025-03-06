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
#include "sw/device/tests/penetrationtests/json/commands.h"
#include "sw/device/tests/penetrationtests/json/crypto_fi_commands.h"
#include "sw/device/tests/penetrationtests/json/ibex_fi_commands.h"
#include "sw/device/tests/penetrationtests/json/lc_ctrl_fi_commands.h"
#include "sw/device/tests/penetrationtests/json/otp_fi_commands.h"
#include "sw/device/tests/penetrationtests/json/rng_fi_commands.h"
#include "sw/device/tests/penetrationtests/json/rom_fi_commands.h"

// Include handlers
#include "fi/crypto_fi.h"
#include "fi/ibex_fi.h"
#include "fi/lc_ctrl_fi.h"
#include "fi/otp_fi.h"
#include "fi/rng_fi.h"
#include "fi/rom_fi.h"
#include "lib/extclk_sca_fi.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

status_t process_cmd(ujson_t *uj) {
  while (true) {
    penetrationtest_cmd_t cmd;
    TRY(ujson_deserialize_penetrationtest_cmd_t(uj, &cmd));
    switch (cmd) {
      case kPenetrationtestCommandCryptoFi:
        RESP_ERR(uj, handle_crypto_fi(uj));
        break;
      case kPenetrationtestCommandExtClkScaFi:
        RESP_ERR(uj, handle_extclk_sca_fi(uj));
        break;
      case kPenetrationtestCommandIbexFi:
        RESP_ERR(uj, handle_ibex_fi(uj));
        break;
      case kPenetrationtestCommandLCCtrlFi:
        RESP_ERR(uj, handle_lc_ctrl_fi(uj));
        break;
      case kPenetrationtestCommandOtpFi:
        RESP_ERR(uj, handle_otp_fi(uj));
        break;
      case kPenetrationtestCommandRngFi:
        RESP_ERR(uj, handle_rng_fi(uj));
        break;
      case kPenetrationtestCommandRomFi:
        RESP_ERR(uj, handle_rom_fi(uj));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", cmd);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_complex_init());
  ujson_t uj = ujson_ottf_console();
  return status_ok(process_cmd(&uj));
}
