// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/drbg.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/crypto/cryptotest/json/drbg_commands.h"

status_t handle_drbg(ujson_t *uj) {
  cryptotest_drbg_input_t uj_input;
  // Deserialize test arguments from UART
  TRY(ujson_deserialize_cryptotest_drbg_input_t(uj, &uj_input));

  // Entropy for initialization
  uint8_t entropy_buf[kEntropySeedBytes];
  memset(entropy_buf, 0, kEntropySeedBytes);
  memcpy(entropy_buf, uj_input.entropy, uj_input.entropy_len);
  otcrypto_const_byte_buf_t entropy = {
      .len = kEntropySeedBytes,
      .data = entropy_buf,
  };

  // Personalization string
  uint8_t perso_string_buf[uj_input.personalization_string_len];
  memcpy(perso_string_buf, uj_input.personalization_string,
         uj_input.personalization_string_len);
  otcrypto_const_byte_buf_t perso_string = {
      .len = uj_input.personalization_string_len,
      .data = perso_string_buf,
  };

  // Reseed entropy
  uint8_t reseed_entropy_buf[uj_input.reseed_entropy_len];
  memcpy(reseed_entropy_buf, uj_input.reseed_entropy,
         uj_input.reseed_entropy_len);
  otcrypto_const_byte_buf_t reseed_entropy = {
      .len = uj_input.reseed_entropy_len,
      .data = uj_input.reseed_entropy,
  };

  // Reseed additional input
  uint8_t reseed_addl_buf[uj_input.reseed_additional_input_len];
  memcpy(reseed_addl_buf, uj_input.reseed_additional_input,
         uj_input.reseed_additional_input_len);
  otcrypto_const_byte_buf_t reseed_addl = {
      .len = uj_input.reseed_additional_input_len,
      .data = uj_input.reseed_additional_input,
  };

  // First additional input
  uint8_t addl_1_buf[uj_input.additional_input_1_len];
  memcpy(addl_1_buf, uj_input.additional_input_1,
         uj_input.additional_input_1_len);
  otcrypto_const_byte_buf_t addl_1 = {
      .len = uj_input.additional_input_1_len,
      .data = uj_input.additional_input_1,
  };

  // Second additional input
  uint8_t addl_2_buf[uj_input.additional_input_2_len];
  memcpy(addl_2_buf, uj_input.additional_input_2,
         uj_input.additional_input_2_len);
  otcrypto_const_byte_buf_t addl_2 = {
      .len = uj_input.additional_input_2_len,
      .data = uj_input.additional_input_2,
  };

  // Buffer for random output
  cryptotest_drbg_output_t uj_output = {
      .output_len = uj_input.output_len,
  };
  size_t output_words = ceil_div(uj_output.output_len, sizeof(uint32_t));
  otcrypto_word32_buf_t output = {
      .len = output_words,
      .data = (uint32_t *)uj_output.output,
  };

  // Instantiate DRBG system. We cannot use the FIPS-compliant APIs
  // because the test vector specifies an entropy string to use.
  TRY(otcrypto_drbg_manual_instantiate(entropy, perso_string));

  // Reseed if the test says we need to
  if (uj_input.reseed) {
    TRY(otcrypto_drbg_manual_reseed(reseed_entropy, reseed_addl));
  }

  // Add first additional input (the test vectors require generating
  // `output_len` bits of output here, but they may be discarded).
  TRY(otcrypto_drbg_manual_generate(addl_1, output));

  // Add second additional input and generate random output
  TRY(otcrypto_drbg_manual_generate(addl_2, output));

  // Uninstantiate the DRBG system
  otcrypto_drbg_uninstantiate();

  // Send output to host via UART
  RESP_OK(ujson_serialize_cryptotest_drbg_output_t, uj, &uj_output);
  return OK_STATUS(0);
}
