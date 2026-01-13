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

#include "hw/top/aes_regs.h"  // Generated.
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
  /**
   * Max. number of AAD or PTX blocks supported by the AES-GCM tests.
   */
  kMaxGcmBlocks = 4,
  /**
   * Number of cycles we are putting Ibex into sleep mode. In the meanwhile,
   * AES-GCM executes and we are measuring the power consumption of the
   * operation. The number of cycles were determined by using ibex_mcycle_read()
   * between calling dif_aes_trigger() and waiting until the IDLE bit has been
   * seen. Here, up to 300 cycles were measured. Moreover, we are using a start
   * trigger delay of 320.
   */
  kIbexAesGcmSleepCycles = 1000,
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

static status_t trigger_aes_gcm(dif_aes_key_share_t key, dif_aes_iv_t iv,
                                dif_aes_data_t aad[kMaxGcmBlocks],
                                size_t aad_num_blocks,
                                size_t aad_last_block_size,
                                dif_aes_data_t ptx[kMaxGcmBlocks],
                                size_t ptx_num_blocks,
                                size_t ptx_last_block_size, dif_aes_data_t *tag,
                                aes_sca_gcm_triggers_t trigger) {
  // AES GCM configuration used for this test.
  dif_aes_transaction_t transaction_gcm = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeGcm,
      .key_len = kDifAesKey128,
      .key_provider = kDifAesKeySoftwareProvided,
      .manual_operation = kDifAesManualOperationManual,
      .mask_reseeding = kDifAesReseedPer8kBlock,
      .reseed_on_key_change = false,
      .force_masks = transaction.force_masks,
      .ctrl_aux_lock = false,
  };

  // Write the initial key share, IV and data in CSRs.
  TRY(dif_aes_start(&aes, &transaction_gcm, &key, &iv));

#if !OT_IS_ENGLISH_BREAKFAST
  if (transaction.force_masks) {
    // Disable masking. Force the masking PRNG output value to 0.
    TRY(aes_sca_load_fixed_seed());
  }
#endif

  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kIbexAesGcmSleepCycles * 2);
  // Encrypt all-zero block.
  aes_manual_trigger();
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kIbexAesGcmSleepCycles * 2);
  // Encrypt initial counter block.
  if (trigger.triggers[0]) {
    // In the FPGA mode, the AES automatically raises the trigger signal. For
    // the other mode, the pentest_call_and_sleep function manually raises the
    // trigger pin.
    if (fpga_mode) {
      pentest_set_trigger_high();
    }
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                           !fpga_mode, false);
    if (fpga_mode) {
      pentest_set_trigger_low();
    }
  } else {
    aes_manual_trigger();
  }

  // Process the AAD blocks.
  // For the first block, put the AES-GCM into the AAD phase.
  size_t valid_bytes = 16;
  if (aad_num_blocks == 1) {
    valid_bytes = aad_last_block_size;
  }
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_AAD,
                            valid_bytes));
  for (size_t it = 0; it < aad_num_blocks - 1; it++) {
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                  kIbexAesGcmSleepCycles * 2);
    TRY(dif_aes_load_data(&aes, aad[it]));
    if (trigger.triggers[1] && trigger.block == it) {
      // In the FPGA mode, the AES automatically raises the trigger signal. For
      // the other mode, the pentest_call_and_sleep function manually raises the
      // trigger pin.
      if (fpga_mode) {
        pentest_set_trigger_high();
      }
      pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                             !fpga_mode, false);
      if (fpga_mode) {
        pentest_set_trigger_low();
      }
    } else {
      aes_manual_trigger();
    }
  }

  // For the last block, check if the block size is smaller than 16 bytes. Then
  // we need to again put AES-GCM into the AAD phase with the block size.
  if (aad_num_blocks != 1 && aad_last_block_size != 16) {
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                  kIbexAesGcmSleepCycles * 2);
    TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_AAD,
                              aad_last_block_size));
  }
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_load_data(&aes, aad[aad_num_blocks - 1]));
  if (trigger.triggers[1] && trigger.block == aad_num_blocks - 1) {
    // In the FPGA mode, the AES automatically raises the trigger signal. For
    // the other mode, the pentest_call_and_sleep function manually raises the
    // trigger pin.
    if (fpga_mode) {
      pentest_set_trigger_high();
    }
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                           !fpga_mode, false);
    if (fpga_mode) {
      pentest_set_trigger_low();
    }
  } else {
    aes_manual_trigger();
  }

  // Process the PTX blocks.
  // For the first block, put the AES-GCM into the TEXT phase.
  valid_bytes = 16;
  if (ptx_num_blocks == 1) {
    valid_bytes = ptx_last_block_size;
  }
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TEXT,
                            valid_bytes));
  for (size_t it = 0; it < ptx_num_blocks - 1; it++) {
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                  kIbexAesGcmSleepCycles * 2);
    TRY(dif_aes_load_data(&aes, ptx[it]));
    if (trigger.triggers[2] && trigger.block == it) {
      // In the FPGA mode, the AES automatically raises the trigger signal. For
      // the other mode, the pentest_call_and_sleep function manually raises the
      // trigger pin.
      if (fpga_mode) {
        pentest_set_trigger_high();
      }
      pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                             !fpga_mode, false);
      if (fpga_mode) {
        pentest_set_trigger_low();
      }
    } else {
      aes_manual_trigger();
    }
  }
  // For the last block, check if the block size is smaller than 16 bytes. Then
  // we need to again put AES-GCM into the TEXT phase with the block size.
  if (ptx_num_blocks != 1 && ptx_last_block_size != 16) {
    AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                  kIbexAesGcmSleepCycles * 2);
    TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TEXT,
                              ptx_last_block_size));
  }
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_load_data(&aes, ptx[ptx_num_blocks - 1]));
  if (trigger.triggers[2] && trigger.block == ptx_num_blocks - 1) {
    // In the FPGA mode, the AES automatically raises the trigger signal. For
    // the other mode, the pentest_call_and_sleep function manually raises the
    // trigger pin.
    if (fpga_mode) {
      pentest_set_trigger_high();
    }
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                           !fpga_mode, false);
    if (fpga_mode) {
      pentest_set_trigger_low();
    }
  } else {
    aes_manual_trigger();
  }

  // Generate tag.
  size_t ptx_total_bytes = (ptx_num_blocks - 1) * 16 + ptx_last_block_size;
  size_t aad_total_bytes = (aad_num_blocks - 1) * 16 + aad_last_block_size;
  uint64_t len_ptx = ptx_total_bytes * 8;
  uint64_t len_aad = aad_total_bytes * 8;
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusIdle, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_set_gcm_phase(&aes, AES_CTRL_GCM_SHADOWED_PHASE_VALUE_GCM_TAG,
                            16));
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_load_gcm_tag_len(&aes, len_ptx, len_aad));
  if (trigger.triggers[3]) {
    // In the FPGA mode, the AES automatically raises the trigger signal. For
    // the other mode, the pentest_call_and_sleep function manually raises the
    // trigger pin.
    if (fpga_mode) {
      pentest_set_trigger_high();
    }
    pentest_call_and_sleep(aes_manual_trigger, kIbexAesGcmSleepCycles,
                           !fpga_mode, false);
    if (fpga_mode) {
      pentest_set_trigger_low();
    }
  } else {
    aes_manual_trigger();
  }

  // Read the TAG block from the AES.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusOutputValid, true,
                                kIbexAesGcmSleepCycles * 2);
  TRY(dif_aes_read_output(&aes, tag));

  return OK_STATUS();
}

status_t handle_aes_sca_gcm_fvsr_batch(ujson_t *uj) {
  // Receive the AES-GCM input data over uJSON.
  aes_sca_num_ops_t uj_num_ops;
  aes_sca_gcm_triggers_t uj_triggers;
  aes_sca_block_t uj_iv;
  aes_sca_key_t uj_key;
  aes_sca_num_blocks_t uj_aad_blocks;
  aes_sca_num_blocks_t uj_ptx_blocks;
  aes_sca_block_t uj_aad[kMaxGcmBlocks];
  aes_sca_block_t uj_ptx[kMaxGcmBlocks];
  // Get number of batch iterations.
  TRY(ujson_deserialize_aes_sca_num_ops_t(uj, &uj_num_ops));
  if (uj_num_ops.num_batch_ops > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }
  // Get the trigger configuration.
  // uj_triggers.triggers[0] = True/False - process initial counter block.
  // uj_triggers.triggers[1] = True/False - process AAD blocks.
  // uj_triggers.triggers[2] = True/False - process PTX blocks.
  // uj_triggers.triggers[3] = True/False - process TAG block.
  // uj_triggers.block = int - which AAD or PTX block is captured?
  TRY(ujson_deserialize_aes_sca_gcm_triggers_t(uj, &uj_triggers));
  // Get fixed IV and fixed KEY.
  TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_iv));
  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  // Get number of AAD and PTX blocks we are expecting.
  TRY(ujson_deserialize_aes_sca_num_blocks_t(uj, &uj_aad_blocks));
  TRY(ujson_deserialize_aes_sca_num_blocks_t(uj, &uj_ptx_blocks));
  if (uj_aad_blocks.num_blocks > kMaxGcmBlocks ||
      uj_ptx_blocks.num_blocks > kMaxGcmBlocks) {
    return ABORTED();
  }
  // Fetch all AAD blocks.
  for (size_t it = 0; it < uj_aad_blocks.num_blocks; it++) {
    TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_aad[it]));
  }
  // Fetch all PTX blocks.
  for (size_t it = 0; it < uj_ptx_blocks.num_blocks; it++) {
    TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_ptx[it]));
  }

  // Prepare fixed AES IV.
  dif_aes_iv_t aes_iv_fixed;
  memset(aes_iv_fixed.iv, 0, 16);
  memcpy(aes_iv_fixed.iv, uj_iv.block, uj_iv.num_valid_bytes);

  // Generate Fvsr AES IV & key set.
  dif_aes_iv_t aes_iv_fvsr[kNumBatchOpsMax];
  uint8_t batch_keys[kNumBatchOpsMax][kAesKeyLength];
  bool sample_fixed = true;
  for (size_t it = 0; it < uj_num_ops.num_batch_ops; it++) {
    memset(aes_iv_fvsr[it].iv, 0, 16);
    memset(batch_keys[it], 0, kAesKeyLength);
    if (sample_fixed) {
      memcpy(aes_iv_fvsr[it].iv, aes_iv_fixed.iv, uj_iv.num_valid_bytes);
      memcpy(batch_keys[it], uj_key.key, uj_key.key_length);
    } else {
      // Generate random IV.
      uint8_t rand_iv[16];
      prng_rand_bytes(rand_iv, 16);
      memcpy(aes_iv_fvsr[it].iv, rand_iv, uj_iv.num_valid_bytes);
      // Generate random key.
      prng_rand_bytes(batch_keys[it], uj_key.key_length);
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  // Prepare batch key structure.
  dif_aes_key_share_t key_fvsr[kNumBatchOpsMax];
  for (size_t it = 0; it < uj_num_ops.num_batch_ops; it++) {
    memset(key_fvsr[it].share0, 0, sizeof(key_fvsr[it].share0));
    memset(key_fvsr[it].share1, 0, sizeof(key_fvsr[it].share1));

    // Mask the provided key.
    for (int i = 0; i < uj_key.key_length / 4; ++i) {
      key_fvsr[it].share1[i] = pentest_non_linear_layer(
          pentest_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking)));
      key_fvsr[it].share0[i] =
          *((uint32_t *)batch_keys[it] + i) ^ key_fvsr[it].share1[i];
    }
    // Provide random shares for unused key bits.
    for (size_t i = uj_key.key_length / 4; i < kAesKeyLengthMax / 4; ++i) {
      key_fvsr[it].share1[i] =
          pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
      key_fvsr[it].share0[i] =
          pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
    }
  }

  // Prepare the fixed AAD.
  dif_aes_data_t aes_aad[kMaxGcmBlocks];
  size_t aes_aad_last_block_size = 0;
  for (size_t it = 0; it < uj_aad_blocks.num_blocks; it++) {
    memset(aes_aad[it].data, 0, sizeof(aes_aad[it].data));
    memcpy(aes_aad[it].data, uj_aad[it].block, uj_aad[it].num_valid_bytes);
    aes_aad_last_block_size = uj_aad[it].num_valid_bytes;
  }

  // Prepare the fixed plaintext.
  dif_aes_data_t aes_ptx[kMaxGcmBlocks];
  size_t aes_ptx_last_block_size = 0;
  for (size_t it = 0; it < uj_ptx_blocks.num_blocks; it++) {
    memset(aes_ptx[it].data, 0, sizeof(aes_ptx[it].data));
    memcpy(aes_ptx[it].data, uj_ptx[it].block, uj_ptx[it].num_valid_bytes);
    aes_ptx_last_block_size = uj_ptx[it].num_valid_bytes;
  }

  // Trigger the AES GCM operation.
  dif_aes_data_t aes_tag_acc;
  aes_tag_acc.data[0] = 0;
  aes_tag_acc.data[1] = 0;
  aes_tag_acc.data[2] = 0;
  aes_tag_acc.data[3] = 0;
  for (size_t it = 0; it < uj_num_ops.num_batch_ops; it++) {
    dif_aes_data_t aes_tag;
    TRY(trigger_aes_gcm(key_fvsr[it], aes_iv_fvsr[it], aes_aad,
                        uj_aad_blocks.num_blocks, aes_aad_last_block_size,
                        aes_ptx, uj_ptx_blocks.num_blocks,
                        aes_ptx_last_block_size, &aes_tag, uj_triggers));
    // Accumulate (i.e., XOR) TAG for sending back to host.
    for (size_t i = 0; i < ARRAYSIZE(aes_tag_acc.data); i++) {
      aes_tag_acc.data[i] ^= aes_tag.data[i];
    }
  }

  // Send accumulated TAG back to host.
  aes_sca_block_t uj_tag;
  uj_tag.num_valid_bytes = 16;
  memset(uj_tag.block, 0, sizeof(uj_tag.block));
  memcpy(uj_tag.block, (uint8_t *)aes_tag_acc.data, uj_tag.num_valid_bytes);

  RESP_OK(ujson_serialize_aes_sca_block_t, uj, &uj_tag);

  return OK_STATUS();
}

status_t handle_aes_sca_gcm_single_encrypt(ujson_t *uj) {
  // Receive the AES-GCM input data over uJSON.
  aes_sca_gcm_triggers_t uj_triggers;
  aes_sca_block_t uj_iv;
  aes_sca_key_t uj_key;
  aes_sca_num_blocks_t uj_aad_blocks;
  aes_sca_num_blocks_t uj_ptx_blocks;
  aes_sca_block_t uj_aad[kMaxGcmBlocks];
  aes_sca_block_t uj_ptx[kMaxGcmBlocks];
  // Get the trigger configuration.
  // uj_triggers.triggers[0] = True/False - process initial counter block.
  // uj_triggers.triggers[1] = True/False - process AAD blocks.
  // uj_triggers.triggers[2] = True/False - process PTX blocks.
  // uj_triggers.triggers[3] = True/False - process TAG block.
  // uj_triggers.block = int - which AAD or PTX block is captured?
  TRY(ujson_deserialize_aes_sca_gcm_triggers_t(uj, &uj_triggers));
  // Get IV and KEY.
  TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_iv));
  TRY(ujson_deserialize_aes_sca_key_t(uj, &uj_key));
  // Get number of AAD and PTX blocks we are expecting.
  TRY(ujson_deserialize_aes_sca_num_blocks_t(uj, &uj_aad_blocks));
  TRY(ujson_deserialize_aes_sca_num_blocks_t(uj, &uj_ptx_blocks));
  if (uj_aad_blocks.num_blocks > kMaxGcmBlocks ||
      uj_ptx_blocks.num_blocks > kMaxGcmBlocks) {
    return ABORTED();
  }
  // Fetch all AAD blocks.
  for (size_t it = 0; it < uj_aad_blocks.num_blocks; it++) {
    TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_aad[it]));
  }
  // Fetch all PTX blocks.
  for (size_t it = 0; it < uj_ptx_blocks.num_blocks; it++) {
    TRY(ujson_deserialize_aes_sca_block_t(uj, &uj_ptx[it]));
  }

  // Prepare AES IV.
  dif_aes_iv_t aes_iv;
  memset(aes_iv.iv, 0, 16);
  memcpy(aes_iv.iv, uj_iv.block, uj_iv.num_valid_bytes);

  // Prepare keys.
  dif_aes_key_share_t key;
  memset(key.share0, 0, sizeof(key.share0));
  memset(key.share1, 0, sizeof(key.share1));

  // Mask the provided key.
  for (int i = 0; i < uj_key.key_length / 4; ++i) {
    key.share1[i] = pentest_non_linear_layer(
        pentest_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking)));
    key.share0[i] = *((uint32_t *)uj_key.key + i) ^ key.share1[i];
  }
  // Provide random shares for unused key bits.
  for (size_t i = uj_key.key_length / 4; i < kAesKeyLengthMax / 4; ++i) {
    key.share1[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
    key.share0[i] =
        pentest_non_linear_layer(pentest_next_lfsr(1, kPentestLfsrMasking));
  }

  // Prepare the AAD.
  dif_aes_data_t aes_aad[kMaxGcmBlocks];
  size_t aes_aad_last_block_size = 0;
  for (size_t it = 0; it < uj_aad_blocks.num_blocks; it++) {
    memset(aes_aad[it].data, 0, sizeof(aes_aad[it].data));
    memcpy(aes_aad[it].data, uj_aad[it].block, uj_aad[it].num_valid_bytes);
    aes_aad_last_block_size = uj_aad[it].num_valid_bytes;
  }

  // Prepare the plaintext.
  dif_aes_data_t aes_ptx[kMaxGcmBlocks];
  size_t aes_ptx_last_block_size = 0;
  for (size_t it = 0; it < uj_ptx_blocks.num_blocks; it++) {
    memset(aes_ptx[it].data, 0, sizeof(aes_ptx[it].data));
    memcpy(aes_ptx[it].data, uj_ptx[it].block, uj_ptx[it].num_valid_bytes);
    aes_ptx_last_block_size = uj_ptx[it].num_valid_bytes;
  }

  // Trigger the AES GCM operation.
  dif_aes_data_t aes_tag;
  TRY(trigger_aes_gcm(key, aes_iv, aes_aad, uj_aad_blocks.num_blocks,
                      aes_aad_last_block_size, aes_ptx,
                      uj_ptx_blocks.num_blocks, aes_ptx_last_block_size,
                      &aes_tag, uj_triggers));

  // Send TAG back to host.
  aes_sca_block_t uj_tag;
  uj_tag.num_valid_bytes = 16;
  memset(uj_tag.block, 0, sizeof(uj_tag.block));
  memcpy(uj_tag.block, (uint8_t *)aes_tag.data, uj_tag.num_valid_bytes);

  RESP_OK(ujson_serialize_aes_sca_block_t, uj, &uj_tag);

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
    case kAesScaSubcommandGcmFvsrBatch:
      return handle_aes_sca_gcm_fvsr_batch(uj);
    case kAesScaSubcommandGcmSingleEncrypt:
      return handle_aes_sca_gcm_single_encrypt(uj);
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
