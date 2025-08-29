// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

OTTF_DEFINE_TEST_CONFIG();

typedef struct test_params {
  size_t cert_body_size;
  uint8_t magic_byte;
} test_params_t;

const uint8_t kDiceCwtCoseKeyMagic = 0xa5;
const uint8_t kDiceCwtCoseSign1Magic = 0x84;

static const test_params_t kTestCases[] = {{
                                               0,
                                               kDiceCwtCoseKeyMagic,
                                           },
                                           {
                                               1,
                                               kDiceCwtCoseKeyMagic,
                                           },
                                           {
                                               1,
                                               kDiceCwtCoseSign1Magic,
                                           }};

status_t invalid_cert_size_test(void) {
  for (size_t i = 0; i < ARRAYSIZE(kTestCases); ++i) {
    uint8_t cert_body_p = kTestCases[i].magic_byte;
    const perso_tlv_cert_obj_t cert_obj = {
        .cert_body_size = kTestCases[i].cert_body_size,
        .cert_body_p = &cert_body_p,
    };
    const hmac_digest_t pubkey_id = {0};
    const ecdsa_p256_public_key_t pubkey = {0};
    hardened_bool_t cert_valid_output = kHardenedBoolFalse;
    rom_error_t error = dice_cert_check_valid(&cert_obj, &pubkey_id, &pubkey,
                                              &cert_valid_output);
    TRY_CHECK(error == kErrorDiceCwtCoseKeyNotFound);
  }
  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, invalid_cert_size_test);
  return status_ok(result);
}
