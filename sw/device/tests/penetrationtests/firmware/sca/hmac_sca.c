// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/hmac_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/hmac_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

enum {
  /**
   * Key length in bytes.
   */
  kKeyLength = HMACSCA_CMD_MAX_KEY_BYTES,
  /**
   * Message length in bytes.
   */
  kMessageLength = HMACSCA_CMD_MAX_MESSAGE_BYTES,
  /**
   * Tag length in bytes.
   */
  kTagLength = HMACSCA_CMD_MAX_TAG_BYTES,
  /**
   * Tag length in words.
   */
  kTagLengthWord = kTagLength / sizeof(uint32_t),
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 128,
};

static status_t trigger_hmac(uint8_t key_buf[], uint8_t mask_buf[],
                             uint8_t msg_buf[], uint32_t tag_buf[]) {
  // Build the key configuration
  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_length = kKeyLength,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // Create keyblob.
  uint32_t keyblob[keyblob_num_words(config)];

  // Create blinded key.
  TRY(keyblob_from_key_and_mask((uint32_t *)key_buf, (uint32_t *)mask_buf,
                                config, keyblob));
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Create input message.
  otcrypto_const_byte_buf_t input_message = {
      .len = kMessageLength,
      .data = msg_buf,
  };

  // Create tag.
  otcrypto_word32_buf_t tag = {
      .len = kTagLengthWord,
      .data = tag_buf,
  };

  pentest_set_trigger_high();
  TRY(otcrypto_hmac(&key, input_message, tag));
  pentest_set_trigger_low();
  return OK_STATUS();
}

status_t handle_hmac_pentest_init(ujson_t *uj) {
  // Setup trigger and enable peripherals needed for the test.
  pentest_select_trigger_type(kPentestTriggerTypeSw);
  // Enable the HMAC module and disable unused IP blocks to improve
  // SCA measurements.
  pentest_init(kPentestTriggerSourceHmac,
               kPentestPeripheralEntropy | kPentestPeripheralIoDiv4 |
                   kPentestPeripheralOtbn | kPentestPeripheralCsrng |
                   kPentestPeripheralEdn | kPentestPeripheralHmac);

  // Disable the instruction cache and dummy instructions for SCA.
  pentest_configure_cpu();

  // Read device ID and return to host.
  penetrationtest_device_id_t uj_output;
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_id_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_hmac_sca_batch_fvsr(ujson_t *uj) {
  penetrationtest_hmac_sca_key_t uj_key;
  penetrationtest_hmac_sca_num_it_t uj_it;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_num_it_t(uj, &uj_it));

  uint8_t batch_messages[kNumBatchOpsMax][kMessageLength];
  uint8_t batch_keys[kNumBatchOpsMax][kKeyLength];
  uint8_t batch_masks[kNumBatchOpsMax][kKeyLength];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key/masks is used and the message is random. When
  // not sample_fixed, a random key/mask and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_key.key, kKeyLength);
      memcpy(batch_masks[it], uj_key.mask, kKeyLength);
    } else {
      prng_rand_bytes(batch_keys[it], kKeyLength);
      prng_rand_bytes(batch_masks[it], kKeyLength);
    }
    prng_rand_bytes(batch_messages[it], kMessageLength);
    sample_fixed = batch_messages[it][0] & 0x1;
  }

  // Invoke HMAC for each data set.
  uint32_t tag_buf[kTagLengthWord];
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    TRY(trigger_hmac(batch_keys[it], batch_masks[it], batch_messages[it],
                     tag_buf));
  }

  // Send the last tag to host via UART.
  penetrationtest_hmac_sca_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, kTagLength);
  RESP_OK(ujson_serialize_penetrationtest_hmac_sca_tag_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_hmac_sca_batch_random(ujson_t *uj) {
  penetrationtest_hmac_sca_num_it_t uj_it;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_num_it_t(uj, &uj_it));

  uint8_t batch_messages[kNumBatchOpsMax][kMessageLength];
  uint8_t batch_keys[kNumBatchOpsMax][kKeyLength];
  uint8_t batch_masks[kNumBatchOpsMax][kKeyLength];

  // Generate random keys and messages.
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    prng_rand_bytes(batch_keys[it], kKeyLength);
    prng_rand_bytes(batch_masks[it], kKeyLength);
    prng_rand_bytes(batch_messages[it], kMessageLength);
  }

  // Invoke HMAC for each data set.
  uint32_t tag_buf[kTagLengthWord];
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    TRY(trigger_hmac(batch_keys[it], batch_masks[it], batch_messages[it],
                     tag_buf));
  }

  // Send the last tag to host via UART.
  penetrationtest_hmac_sca_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, kTagLength);
  RESP_OK(ujson_serialize_penetrationtest_hmac_sca_tag_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_hmac_sca_single(ujson_t *uj) {
  penetrationtest_hmac_sca_key_t uj_key;
  penetrationtest_hmac_sca_message_t uj_message;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_message_t(uj, &uj_message));

  // Create buffer to store key, mask, message, and tag.
  uint8_t key_buf[kKeyLength];
  memcpy(key_buf, uj_key.key, kKeyLength);
  uint8_t mask_buf[kKeyLength];
  memcpy(mask_buf, uj_key.mask, kKeyLength);
  uint8_t msg_buf[kMessageLength];
  memcpy(msg_buf, uj_message.message, kMessageLength);
  uint32_t tag_buf[kTagLengthWord];

  // Trigger HMAC operation.
  TRY(trigger_hmac(key_buf, mask_buf, msg_buf, tag_buf));

  // Copy tag to uJSON type.
  penetrationtest_hmac_sca_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, kTagLength);

  // Send tag to host via UART.
  RESP_OK(ujson_serialize_penetrationtest_hmac_sca_tag_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_hmac_sca(ujson_t *uj) {
  hmac_sca_subcommand_t cmd;
  TRY(ujson_deserialize_hmac_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kHmacScaSubcommandInit:
      return handle_hmac_pentest_init(uj);
    case kHmacScaSubcommandBatchFvsr:
      return handle_hmac_sca_batch_fvsr(uj);
    case kHmacScaSubcommandBatchRandom:
      return handle_hmac_sca_batch_random(uj);
    case kHmacScaSubcommandSingle:
      return handle_hmac_sca_single(uj);
    default:
      LOG_ERROR("Unrecognized HMAC SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
