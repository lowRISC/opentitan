// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/hmac_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/hmac_testutils.h"
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

static dif_hmac_t hmac;

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessBig,
    .message_endianness = kDifHmacEndiannessLittle,
};

static status_t trigger_hmac(uint8_t key_buf[], uint8_t msg_buf[],
                             uint32_t tag_buf[],
                             penetrationtest_hmac_sca_triggers_t uj_triggers) {
  uint8_t inverted_key_buff[kKeyLength] = {0};

  for (int i = 0; i < kKeyLength; i++) {
    inverted_key_buff[i] = key_buf[31 - i];
  }

  dif_hmac_digest_t digest;

  if (uj_triggers.start_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_hmac_mode_hmac_start(&hmac, inverted_key_buff,
                               kHmacTransactionConfig));
  if (uj_triggers.start_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_triggers.msg_trigger) {
    pentest_set_trigger_high();
  }
  TRY(hmac_testutils_push_message(&hmac, (char *)msg_buf, kMessageLength));
  if (uj_triggers.msg_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_triggers.process_trigger) {
    pentest_set_trigger_high();
  }
  TRY(dif_hmac_process(&hmac));
  if (uj_triggers.process_trigger) {
    pentest_set_trigger_low();
  }

  if (uj_triggers.finish_trigger) {
    pentest_set_trigger_high();
  }
  TRY(hmac_testutils_finish_polled(&hmac, &digest));
  if (uj_triggers.finish_trigger) {
    pentest_set_trigger_low();
  }

  // memcpy(tag_buf, digest.digest, kTagLength);
  for (int i = 0; i < kTagLengthWord; i++) {
    tag_buf[i] = digest.digest[7 - i];
  }

  return OK_STATUS();
}

status_t handle_hmac_pentest_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_cpuctrl_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_cpuctrl_data));
  penetrationtest_sensor_config_t uj_sensor_data;
  TRY(ujson_deserialize_penetrationtest_sensor_config_t(uj, &uj_sensor_data));

  // Setup trigger and enable peripherals needed for the test.
  pentest_select_trigger_type(kPentestTriggerTypeSw);

  // Disable the instruction cache and dummy instructions for SCA.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_cpuctrl_data.enable_icache, &uj_output.icache_en,
      uj_cpuctrl_data.enable_dummy_instr, &uj_output.dummy_instr_en,
      uj_cpuctrl_data.dummy_instr_count, uj_cpuctrl_data.enable_jittery_clock,
      uj_cpuctrl_data.enable_sram_readback, &uj_output.clock_jitter_locked,
      &uj_output.clock_jitter_en, &uj_output.sram_main_readback_locked,
      &uj_output.sram_ret_readback_locked, &uj_output.sram_main_readback_en,
      &uj_output.sram_ret_readback_en, uj_cpuctrl_data.enable_data_ind_timing,
      &uj_output.data_ind_timing_en));

  // Enable the HMAC module and disable unused IP blocks to improve
  // SCA measurements.
  pentest_init(kPentestTriggerSourceHmac,
               kPentestPeripheralIoDiv4 | kPentestPeripheralHmac,
               uj_sensor_data.sensor_ctrl_enable,
               uj_sensor_data.sensor_ctrl_en_fatal);

  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  TRY(dif_hmac_init(base_addr, &hmac));

  // Read rom digest.
  TRY(pentest_read_rom_digest(uj_output.rom_digest));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  // Read different SKU config fields and return to host.
  TRY(pentest_send_sku_config(uj));

  return OK_STATUS();
}

status_t handle_hmac_sca_batch_fvsr(ujson_t *uj) {
  penetrationtest_hmac_sca_key_t uj_key;
  penetrationtest_hmac_sca_num_it_t uj_it;
  penetrationtest_hmac_sca_triggers_t uj_triggers;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_num_it_t(uj, &uj_it));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_triggers_t(uj, &uj_triggers));

  uint8_t batch_messages[kNumBatchOpsMax][kMessageLength];
  uint8_t batch_keys[kNumBatchOpsMax][kKeyLength];

  // First generate all FvsR data sets. When sample_fixed,
  // the provided key is used and the message is random. When
  // not sample_fixed, a random key and a random message is
  // generated.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_key.key, kKeyLength);
    } else {
      prng_rand_bytes(batch_keys[it], kKeyLength);
    }
    prng_rand_bytes(batch_messages[it], kMessageLength);
    sample_fixed = batch_messages[it][0] & 0x1;
  }

  // Invoke HMAC for each data set.
  uint32_t tag_buf[kTagLengthWord];
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    TRY(trigger_hmac(batch_keys[it], batch_messages[it], tag_buf, uj_triggers));
  }

  // Send the last tag to host via UART.
  penetrationtest_hmac_sca_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, kTagLength);
  RESP_OK(ujson_serialize_penetrationtest_hmac_sca_tag_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_hmac_sca_batch_random(ujson_t *uj) {
  penetrationtest_hmac_sca_num_it_t uj_it;
  penetrationtest_hmac_sca_triggers_t uj_triggers;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_num_it_t(uj, &uj_it));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_triggers_t(uj, &uj_triggers));

  uint8_t batch_messages[kNumBatchOpsMax][kMessageLength];
  uint8_t batch_keys[kNumBatchOpsMax][kKeyLength];

  // Generate random keys and messages.
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    prng_rand_bytes(batch_keys[it], kKeyLength);
    prng_rand_bytes(batch_messages[it], kMessageLength);
  }

  // Invoke HMAC for each data set.
  uint32_t tag_buf[kTagLengthWord];
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    TRY(trigger_hmac(batch_keys[it], batch_messages[it], tag_buf, uj_triggers));
  }

  // Send the last tag to host via UART.
  penetrationtest_hmac_sca_tag_t uj_tag;
  memcpy(uj_tag.tag, tag_buf, kTagLength);
  RESP_OK(ujson_serialize_penetrationtest_hmac_sca_tag_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_hmac_sca_batch_daisy_chain(ujson_t *uj) {
  penetrationtest_hmac_sca_key_t uj_key;
  penetrationtest_hmac_sca_message_t uj_message;
  penetrationtest_hmac_sca_num_it_t uj_it;
  penetrationtest_hmac_sca_triggers_t uj_triggers;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_message_t(uj, &uj_message));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_num_it_t(uj, &uj_it));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_triggers_t(uj, &uj_triggers));

  // Invoke HMAC for each data set.
  uint32_t tag_buf[kTagLengthWord];
  uint8_t message_buf[HMACSCA_CMD_MAX_MESSAGE_BYTES];
  memcpy(message_buf, uj_message.message, sizeof(uj_message.message));
  for (size_t it = 0; it < uj_it.num_iterations; it++) {
    TRY(trigger_hmac(uj_key.key, message_buf, tag_buf, uj_triggers));
    // Copy the output of the HMAC to the input
    memcpy(message_buf, tag_buf, HMACSCA_CMD_MAX_MESSAGE_BYTES);
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
  penetrationtest_hmac_sca_triggers_t uj_triggers;

  TRY(ujson_deserialize_penetrationtest_hmac_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_message_t(uj, &uj_message));
  TRY(ujson_deserialize_penetrationtest_hmac_sca_triggers_t(uj, &uj_triggers));

  // Create buffer to store key, message, and tag.
  uint8_t key_buf[kKeyLength];
  memcpy(key_buf, uj_key.key, kKeyLength);
  uint8_t msg_buf[kMessageLength];
  memcpy(msg_buf, uj_message.message, kMessageLength);
  uint32_t tag_buf[kTagLengthWord];

  // Trigger HMAC operation.
  TRY(trigger_hmac(key_buf, msg_buf, tag_buf, uj_triggers));

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
    case kHmacScaSubcommandBatchDaisy:
      return handle_hmac_sca_batch_daisy_chain(uj);
    case kHmacScaSubcommandSingle:
      return handle_hmac_sca_single(uj);
    default:
      LOG_ERROR("Unrecognized HMAC SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
