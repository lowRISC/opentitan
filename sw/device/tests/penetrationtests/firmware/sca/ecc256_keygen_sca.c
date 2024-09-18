// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/ecc256_keygen_sca.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

enum {
  /**
   * Number of bytes for ECDSA P-256 seeds and masked private keys.
   */
  kEcc256SeedNumBytes = 320 / 8,
  /**
   * Number of 32b words for ECDSA P-256 seeds and masked private keys.
   */
  kEcc256SeedNumWords = kEcc256SeedNumBytes / sizeof(uint32_t),
  /**
   * Number of bytes for ECDSA P-256 point coordinates.
   */
  kEcc256CoordNumBytes = 256 / 8,
  /**
   * Number of 32b words for ECDSA P-256 point coordinates.
   */
  kEcc256CoordNumWords = kEcc256CoordNumBytes / sizeof(uint32_t),
  /**
   * Mode option for the ECDSA keygen app (generates the private key only).
   */
  kEcc256ModePrivateKeyOnly = 1,
  /**
   * Mode option for the ECDSA keygen app (generates the full keypair).
   */
  kEcc256ModeKeypair = 2,
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 256,
  /**
   * Number of cycles that Ibex should sleep to minimize noise during OTBN
   * operations. Caution: This number should be chosen to provide enough time
   * to complete the operation. Otherwise, Ibex might wake up while OTBN is
   * still busy and disturb the capture. This was measured using mcycle_read
   * when otbn_manual_trigger and otbn_busy_wait_for_done get executed.
   */
  kIbexOtbnSleepCycles = 1100,
};

/**
 * App configuration for p256_key_from_seed_sca
 */
const otbn_app_t kOtbnAppP256KeyFromSeed =
    OTBN_APP_T_INIT(p256_key_from_seed_sca);

static const otbn_addr_t kOtbnVarMode =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, mode);
static const otbn_addr_t kOtbnVarSeed0 =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, seed0);
static const otbn_addr_t kOtbnVarSeed1 =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, seed1);
static const otbn_addr_t kOtbnVarD0 =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, d0);
static const otbn_addr_t kOtbnVarD1 =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, d1);

/**
 * An array of seeds to be used in a batch
 */
uint32_t batch_share0[kNumBatchOpsMax][kEcc256SeedNumWords];

/**
 * An array of masks to be used in a batch
 */
uint32_t batch_share1[kNumBatchOpsMax][kEcc256SeedNumWords];

/**
 * Arrays for first and second share of masked private key d to be used in a
 * batch
 */
uint32_t d0_batch[kEcc256SeedNumWords];
uint32_t d1_batch[kEcc256SeedNumWords];

/**
 * Fixed-message indicator.
 *
 * Used in the 'b' (batch capture) command for indicating whether to use fixed
 * or random message.
 */
static bool run_fixed = true;

/**
 * Masking indicator.
 *
 * Used in the 'b' (batch capture) command for indicating whether to use masks.
 */
static bool en_masks = false;

uint32_t ecc256_seed[kEcc256SeedNumWords];

uint32_t ecc256_C[kEcc256SeedNumWords];

uint32_t random_number[kEcc256CoordNumWords];

uint32_t ecc256_fixed_number[kEcc256CoordNumWords];

/**
 * Adds two integers storred in byte arrays.
 *
 * Adds the integer stored in source array to the integer stored in
 * destination aray.
 * The user needs to ensure that dest_len is enough to store the result
 * without overflow.
 *
 * @param[in] dest  Location of the first input array and the result.
 * @param[in] source  Location of the second input array.
 * @param[in] dest_len   Length of the dest array in bytes.
 * @param[in] source_len   Length of the source array in bytes.
 */
static void add_arrays(uint8_t *dest, uint8_t *source, size_t dest_len,
                       size_t source_len) {
  uint16_t temp = 0;

  for (size_t i = 0; i < source_len; i++) {
    temp += (uint16_t)source[i] + dest[i];
    dest[i] = (uint8_t)(temp & 0x00FF);
    temp >>= 8;
  }

  for (size_t i = source_len; i < dest_len; i++) {
    temp += (uint16_t)dest[i];
    dest[i] = (uint8_t)(temp & 0x00FF);
    temp >>= 8;
  }
}

/**
 * Callback wrapper for OTBN manual trigger function.
 */
static void otbn_manual_trigger(void) { otbn_execute(); }

/**
 * Runs the OTBN key generation program.
 *
 * The seed shares must be `kEcc256SeedNumWords` words long.
 *
 * @param[in] mode  Mode parameter (private key only or full keypair).
 * @param[in] seed  Seed for key generation.
 * @param[in] mask  Mask for seed.
 * @return OK or error.
 */
static status_t p256_run_keygen(uint32_t mode, const uint32_t *share0,
                                const uint32_t *share1) {
  // Secure wipe to scramble DMEM.
  TRY(otbn_load_app(kOtbnAppP256KeyFromSeed));

  // Write mode.
  TRY(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode));

  // Write seed shares.
  TRY(otbn_dmem_write(kEcc256SeedNumWords, share0, kOtbnVarSeed0));
  TRY(otbn_dmem_write(kEcc256SeedNumWords, share1, kOtbnVarSeed1));

  // Execute program. Trigger is set inside this function.
  pentest_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles, true, true);

  return OK_STATUS();
}

status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj, &uj_data));

  uint32_t num_traces = uj_data.num_traces;
  uint32_t batch_digest[kEcc256SeedNumWords];

  if (num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // Zero the batch digest.
  for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
    batch_digest[j] = 0;
  }

  for (size_t i = 0; i < num_traces; ++i) {
    // Set mask to a random mask (en_masks = true) or to 0 (en_masks = false).
    if (en_masks) {
      for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = prng_rand_uint32();
      }
    } else {
      for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = 0;
      }
    }

    // If the run is fixed, take the fixed seed received from the host. Else,
    // generate a random seed.
    if (run_fixed) {
      memcpy(batch_share0[i], ecc256_seed, kEcc256SeedNumBytes);
    } else {
      // Here change to random_number + C.
      // It is necessary to set the C first.
      memcpy(batch_share0[i], ecc256_C, kEcc256SeedNumBytes);
      for (size_t j = 0; j < kEcc256CoordNumWords; ++j) {
        random_number[j] = prng_rand_uint32();
      }
      add_arrays((unsigned char *)batch_share0[i],
                 (unsigned char *)random_number, kEcc256SeedNumBytes,
                 kEcc256CoordNumBytes);
    }
    for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_share0[i][j] ^= batch_share1[i][j];
    }
    // Another PRNG run to determine 'run_fixed' for the next cycle.
    run_fixed = prng_rand_uint32() & 0x1;
  }

  for (size_t i = 0; i < num_traces; ++i) {
    TRY(p256_run_keygen(kEcc256ModePrivateKeyOnly, batch_share0[i],
                        batch_share1[i]));

    // Read results.
    TRY(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0_batch));
    TRY(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1_batch));

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all d0 shares of
    // the batch.
    for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_digest[j] ^= d0_batch[j];
    }
  }
  // Send the batch digest to the host for verification.
  penetrationtest_otbn_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest,
         kEcc256SeedNumWords * 4);
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_batch_digest_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj, &uj_data));

  uint32_t num_traces = uj_data.num_traces;
  uint32_t batch_digest[kEcc256SeedNumWords];

  if (num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // Zero the batch digest.
  for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
    batch_digest[j] = 0;
  }

  for (size_t i = 0; i < num_traces; ++i) {
    // Set mask to a random mask (en_masks = true) or to 0 (en_masks = false).
    if (en_masks) {
      for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = prng_rand_uint32();
      }
    } else {
      for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = 0;
      }
    }

    // If the run is fixed, take the fixed seed received from the host. Else,
    // generate a random seed.
    if (run_fixed) {
      memcpy(batch_share0[i], ecc256_seed, kEcc256SeedNumBytes);
    } else {
      for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share0[i][j] = prng_rand_uint32();
      }
    }

    for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_share0[i][j] ^= batch_share1[i][j];
    }
    run_fixed = prng_rand_uint32() & 0x1;
  }

  for (size_t i = 0; i < num_traces; ++i) {
    TRY(p256_run_keygen(kEcc256ModePrivateKeyOnly, batch_share0[i],
                        batch_share1[i]));

    // Read results.
    TRY(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0_batch));
    TRY(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1_batch));

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all d0 shares of
    // the batch.
    for (size_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_digest[j] ^= d0_batch[j];
    }
  }

  // Send the batch digest to the host for verification.
  penetrationtest_otbn_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest,
         kEcc256SeedNumWords * 4);
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_batch_digest_t, uj,
          &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_sca_ecc256_en_masks(ujson_t *uj) {
  penetrationtest_otbn_sca_en_masks_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_en_masks_t(uj, &uj_data));
  if (uj_data.en_masks) {
    en_masks = true;
  } else {
    en_masks = false;
  }
  return OK_STATUS();
}

status_t handle_otbn_sca_ecc256_set_c(ujson_t *uj) {
  penetrationtest_otbn_sca_constant_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_constant_t(uj, &uj_data));

  memcpy(ecc256_C, uj_data.constant, kEcc256SeedNumBytes);

  return OK_STATUS();
}

status_t handle_otbn_sca_ecc256_set_seed(ujson_t *uj) {
  penetrationtest_otbn_sca_seed_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_seed_t(uj, &uj_data));

  memcpy(ecc256_seed, uj_data.seed, kEcc256SeedNumBytes);

  return OK_STATUS();
}
