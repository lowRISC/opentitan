// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/aes_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/aes.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/aes_sca_commands.h"
#include "sw/device/tests/penetrationtests/json/commands.h"

#ifndef OPENTITAN_IS_ENGLISHBREAKFAST
#include "sw/device/lib/testing/aes_testutils.h"
#endif

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Enable FPGA mode.
 */
static bool fpga_mode = false;

enum {
  kAesKeyLengthMax = 32,
  kAesKeyLength = 16,
  kAesTextLength = 16,
  kTestTimeout = (1000 * 1000),
  /**
   * Number of cycles (at `kClockFreqCpuHz`) that Ibex should sleep to minimize
   * noise during AES operations. Caution: This number should be chosen to
   * provide enough time. Otherwise, Ibex might wake up while AES is still busy
   * and disturb the capture. Currently, we use a start trigger delay of 320
   * clock cycles and the scope captures 60 clock cycles at kClockFreqCpuHz.
   */
  kIbexAesSleepCycles = 680,
  /**
   * The maximum number of encryptions to do per batch. The ChipWhisperer Husky
   * scope determines how many encryptions (capture segments) it wants to record
   * per batch based on the number of samples per segment. As the plaintexts
   * and keys are generated in advance for fixed-vs-random batch captures, we
   * need to make sure the corresponding buffers are sufficiently large. Note
   * that on both CW305 and CW310, the main SRAM has a size of 128 kBytes. So it
   * should be fine to allocate space for 256 segments (2 * 16 Bytes * 256 = 8
   * kBytes).
   */
  kNumBatchOpsMax = 256,
};

static dif_aes_t aes;

dif_aes_transaction_t transaction = {
    .operation = kDifAesOperationEncrypt,
    .mode = kDifAesModeEcb,
    .key_len = kDifAesKey128,
    .manual_operation = kDifAesManualOperationManual,
    .key_provider = kDifAesKeySoftwareProvided,
    .mask_reseeding = kDifAesReseedPer8kBlock,
    .reseed_on_key_change = false,
    .force_masks = false,
    .ctrl_aux_lock = false,
};

/**
 * Load fixed seed into AES.
 *
 * Before calling this function, use
 * aes_testutils_masking_prng_zero_output_seed() to initialize the entropy
 * complex for performing AES SCA measurements with masking switched off. This
 * function then loads the fixed seed into the AES, allowing the disable the
 * masking.
 *
 * @param key Key.
 * @param key_len Key length.
 */
static status_t aes_sca_load_fixed_seed(void) {
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);
  // Load magic seed such that masking is turned off. We need to do this after
  // dif_aes_start() as then the force_masks is correctly set.
  TRY(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);

  return OK_STATUS();
}

/**
 * Mask and configure key.
 *
 * This function masks the provided key using a software LFSR and then
 * configures the key into the AES peripheral. The masking can be disabled by
 * initializing the LFSR to 0 (see `aes_serial_seed_lfsr()`). The key must be
 * `kAesKeyLength` bytes long.
 *
 * @param key Key.
 * @param key_len Key length.
 */
static status_t aes_key_mask_and_config(const uint8_t *key, size_t key_len) {
  if (key_len != kAesKeyLength) {
    return ABORTED();
  }
  dif_aes_key_share_t key_shares;
  // Mask the provided key.
  for (int i = 0; i < key_len / 4; ++i) {
    key_shares.share1[i] = pentest_non_linear_layer(
        pentest_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking)));
    key_shares.share0[i] = *((uint32_t *)key + i) ^ key_shares.share1[i];
  }
  // Provide random shares for unused key bits.
  for (size_t i = key_len / 4; i < kAesKeyLengthMax / 4; ++i) {
    key_shares.share1[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
    key_shares.share0[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
  }
  TRY(dif_aes_start(&aes, &transaction, &key_shares, NULL));

#ifndef OPENTITAN_IS_ENGLISHBREAKFAST
  if (transaction.force_masks) {
    // Disable masking. Force the masking PRNG output value to 0.
    TRY(aes_sca_load_fixed_seed());
  }
#endif

  return OK_STATUS();
}

/**
 * Callback wrapper for AES manual trigger function.
 */
static void aes_manual_trigger(void) {
  (void)dif_aes_trigger(&aes, kDifAesTriggerStart);
}

/**
 * Encrypts a plaintext using the AES peripheral.
 *
 * This function uses `pentest_call_and_sleep()` from the pentest library to put
 * Ibex to sleep in order to minimize noise during captures. The plaintext must
 * be `kAesTextLength` bytes long.
 *
 * @param plaintext Plaintext.
 * @param plaintext_len Length of the plaintext.
 */
static status_t aes_encrypt(const uint8_t *plaintext, size_t plaintext_len) {
  bool ready = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusInputReady, &ready));
  } while (!ready);

  dif_aes_data_t data;
  if (plaintext_len != sizeof(data.data)) {
    return ABORTED();
  }
  memcpy(data.data, plaintext, plaintext_len);
  TRY(dif_aes_load_data(&aes, data));

  // Start AES operation (this triggers the capture) and go to sleep.
  if (fpga_mode) {
    // On FPGA, the trigger is AND-ed with AES !IDLE and creates a LO-HI-LO per.
    // Activate the GPIO by setting the GPIO.
    pentest_set_trigger_high();
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles, false,
                           false);
    pentest_set_trigger_low();
  } else {
    // On the chip, we need to manually set and unset the trigger. This is done
    // in this function to have the trigger as close as possible to the AES
    // operation.
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesSleepCycles, true,
                           false);
  }
  return OK_STATUS();
}

/**
 * Wait until AES output is valid and then get ciphertext and send it over
 * serial communication.
 *
 * @param only_first_word Send only the first word of the ciphertext.
 */
static status_t aes_send_ciphertext(ujson_t *uj) {
  bool ready = false;
  do {
    TRY(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
  } while (!ready);

  dif_aes_data_t ciphertext;
  if (dif_aes_read_output(&aes, &ciphertext) != kDifOk) {
    return OUT_OF_RANGE();
  }

  aes_sca_ciphertext_t uj_output;
  memset(uj_output.ciphertext, 0, kAesTextLength);
  uj_output.ciphertext_length = kAesTextLength;
  memcpy(uj_output.ciphertext, (uint8_t *)ciphertext.data,
         uj_output.ciphertext_length);
  RESP_OK(ujson_serialize_aes_sca_ciphertext_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_aes_sca_batch_daisy_chain(ujson_t *uj) {
  aes_sca_key_t uj_key;
  aes_sca_text_t uj_text;
  penetrationtest_num_enc_t uj_data;

  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_aes_sca_text_t(uj, &uj_text));
  TRY(ujson_deserialize_penetrationtest_num_enc_t(uj, &uj_data));

  // Mask and write the key
  TRY(aes_key_mask_and_config(uj_key.key, uj_key.key_length));

  dif_aes_data_t ciphertext;
  uint8_t plaintext[uj_key.key_length];
  memcpy(plaintext, uj_text.text, uj_text.text_length);

  for (uint32_t i = 0; i < uj_data.num_enc; ++i) {
    // Encrypt
    TRY(aes_encrypt(plaintext, uj_text.text_length));

    // Get ciphertext
    bool ready = false;
    do {
      TRY(dif_aes_get_status(&aes, kDifAesStatusOutputValid, &ready));
    } while (!ready);

    if (dif_aes_read_output(&aes, &ciphertext)) {
      return ABORTED();
    }

    // Use ciphertext as next plaintext
    memcpy(plaintext, ciphertext.data, uj_text.text_length);
  }

  // send last ciphertext
  aes_sca_ciphertext_t uj_output;
  uj_output.ciphertext_length = kAesTextLength;
  memcpy(uj_output.ciphertext, (uint8_t *)ciphertext.data, kAesTextLength);
  RESP_OK(ujson_serialize_aes_sca_ciphertext_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_aes_sca_batch_fvsr_data(ujson_t *uj) {
  aes_sca_key_t uj_key;
  aes_sca_text_t uj_text;
  penetrationtest_num_enc_t uj_data;

  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_aes_sca_text_t(uj, &uj_text));
  TRY(ujson_deserialize_penetrationtest_num_enc_t(uj, &uj_data));

  TRY(aes_key_mask_and_config(uj_key.key, uj_key.key_length));

  uint8_t batch_plaintexts[kNumBatchOpsMax][uj_text.text_length];

  // First generate all FvsR data sets.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_data.num_enc; it++) {
    if (sample_fixed) {
      memcpy(batch_plaintexts[it], uj_text.text, uj_text.text_length);
    } else {
      prng_rand_bytes(batch_plaintexts[it], uj_text.text_length);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  for (uint32_t i = 0; i < uj_data.num_enc; ++i) {
    TRY(aes_encrypt(batch_plaintexts[i], uj_text.text_length));
  }

  TRY(aes_send_ciphertext(uj));

  return OK_STATUS();
}

status_t handle_aes_sca_batch_fvsr_key(ujson_t *uj) {
  aes_sca_key_t uj_key;
  penetrationtest_num_enc_t uj_data;

  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_num_enc_t(uj, &uj_data));

  uint8_t batch_plaintexts[kNumBatchOpsMax][kAesKeyLength];
  uint8_t batch_keys[kNumBatchOpsMax][uj_key.key_length];

  // First generate all FvsR data sets.
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_data.num_enc; it++) {
    if (sample_fixed) {
      memcpy(batch_keys[it], uj_key.key, uj_key.key_length);
    } else {
      prng_rand_bytes(batch_keys[it], uj_key.key_length);
    }
    prng_rand_bytes(batch_plaintexts[it], kAesKeyLength);
    sample_fixed = prng_rand_byte() & 0x1;
  }

  for (uint32_t i = 0; i < uj_data.num_enc; ++i) {
    TRY(aes_key_mask_and_config(batch_keys[i], uj_key.key_length));
    TRY(aes_encrypt(batch_plaintexts[i], kAesKeyLength));
  }

  TRY(aes_send_ciphertext(uj));

  return OK_STATUS();
}

status_t handle_aes_sca_batch_random(ujson_t *uj) {
  aes_sca_key_t uj_key;
  penetrationtest_num_enc_t uj_data;

  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_penetrationtest_num_enc_t(uj, &uj_data));

  TRY(aes_key_mask_and_config(uj_key.key, uj_key.key_length));

  uint8_t batch_plaintexts[kNumBatchOpsMax][kAesKeyLength];

  for (size_t it = 0; it < uj_data.num_enc; it++) {
    prng_rand_bytes(batch_plaintexts[it], kAesKeyLength);
  }

  for (uint32_t i = 0; i < uj_data.num_enc; ++i) {
    TRY(aes_encrypt(batch_plaintexts[i], kAesKeyLength));
  }

  TRY(aes_send_ciphertext(uj));

  return OK_STATUS();
}

status_t handle_aes_sca_single_encrypt(ujson_t *uj) {
  aes_sca_key_t uj_key;
  aes_sca_text_t uj_text;
  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  TRY(ujson_deserialize_aes_sca_text_t(uj, &uj_text));

  TRY(aes_key_mask_and_config(uj_key.key, uj_key.key_length));

  TRY(aes_encrypt(uj_text.text, uj_text.text_length));

  TRY(aes_send_ciphertext(uj));
  return OK_STATUS();
}

status_t handle_aes_pentest_init(ujson_t *uj) {
  // Read mode. FPGA or discrete.
  aes_sca_fpga_mode_t uj_data;
  TRY(ujson_deserialize_aes_sca_fpga_mode_t(uj, &uj_data));
  if (uj_data.fpga_mode == 0x01) {
    fpga_mode = true;
  }

  // Configure the device.
  pentest_setup_device(uj, false, false);

  pentest_init(kPentestTriggerSourceAes,
               kPentestPeripheralIoDiv4 | kPentestPeripheralAes);

  if (dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes) !=
      kDifOk) {
    return ABORTED();
  }

  if (dif_aes_reset(&aes) != kDifOk) {
    return ABORTED();
  }

  return OK_STATUS();
}

status_t handle_aes_pentest_seed_lfsr(ujson_t *uj) {
  aes_sca_lfsr_t uj_lfsr_data;
  TRY(ujson_deserialize_aes_sca_lfsr_t(uj, &uj_lfsr_data));

  uint32_t seed_local = read_32(uj_lfsr_data.seed);
  if (seed_local == 0) {
    // disable masking
    transaction.force_masks = true;
  } else {
    // enable masking
    transaction.force_masks = false;
  }
  pentest_seed_lfsr(seed_local, kPentestLfsrMasking);

#ifndef OPENTITAN_IS_ENGLISHBREAKFAST
  if (transaction.force_masks) {
    LOG_INFO("Disabling masks.");
    const dif_csrng_t csrng = {
        .base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR)};
    const dif_edn_t edn0 = {
        .base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR)};

    status_t res = aes_testutils_masking_prng_zero_output_seed(&csrng, &edn0);
    if (res.value != 0) {
      return ABORTED();
    }
    // Load the magic seed into the PRNG. After this, the PRNG outputs
    // an all-zero vector.
    TRY(aes_sca_load_fixed_seed());
  }
#endif

  TRY(dif_aes_trigger(&aes, kDifAesTriggerDataOutClear));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true, kTestTimeout);
  return OK_STATUS();
}

status_t handle_aes_sca(ujson_t *uj) {
  aes_sca_subcommand_t cmd;
  TRY(ujson_deserialize_aes_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kAesScaSubcommandSingle:
      return handle_aes_sca_single_encrypt(uj);
    case kAesScaSubcommandBatchDaisy:
      return handle_aes_sca_batch_daisy_chain(uj);
    case kAesScaSubcommandBatchRandom:
      return handle_aes_sca_batch_random(uj);
    case kAesScaSubcommandBatchFvsrData:
      return handle_aes_sca_batch_fvsr_data(uj);
    case kAesScaSubcommandBatchFvsrKey:
      return handle_aes_sca_batch_fvsr_key(uj);
    case kAesScaSubcommandInit:
      return handle_aes_pentest_init(uj);
    case kAesScaSubcommandSeedLfsr:
      return handle_aes_pentest_seed_lfsr(uj);
    default:
      LOG_ERROR("Unrecognized AES SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
