// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/crypto/cryptotest/firmware/ecc256_keygen_sca.h"

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/tests/crypto/cryptotest/json/otbn_sca_commands.h"

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
   * still busy and disturb the capture.
   */
  kIbexOtbnSleepCycles = 800,
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
static const otbn_addr_t kOtbnVarX =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, x);
static const otbn_addr_t kOtbnVarY =
    OTBN_ADDR_T_INIT(p256_key_from_seed_sca, y);

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

/**
 * Seed value.
 *
 * The default value corresponds to the test data in
 *   sw/otbn/crypto/test/p256_key_from_seed_test.s
 *
 * This default value can be overwritten via the simpleserial command `x`
 * (see ecc256_set_seed)
 */
uint32_t ecc256_seed[kEcc256SeedNumWords] = {
    0x016064e9, 0x11e3f4d6, 0xac3a6fa7, 0xaba11a1b, 0x8f9271d1,
    0x22b79d5f, 0x1176f31d, 0xb5ac3a51, 0x99a082d7, 0x484eb366,
};

uint32_t ecc256_C[kEcc256SeedNumWords] = {
    0x016064e9, 0x11e3f4d6, 0xac3a6fa7, 0xaba11a1b, 0x8f9271d1,
    0x22b79d5f, 0x1176f31d, 0xb5ac3a51, 0x99a082d7, 0x484eb366,
};

uint32_t random_number[kEcc256CoordNumWords] = {
    0x016064e9, 0x11e3f4d6, 0xac3a6fa7, 0xaba11a1b,
    0x22b79d5f, 0x1176f31d, 0xb5ac3a51, 0x99a082d7,
};

uint32_t ecc256_fixed_number[kEcc256CoordNumWords] = {
    0x04030201, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

/**
 * Enable masks handler.
 *
 * The uJSON data contains:
 *  - en_masks: Enable masks.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_en_masks(ujson_t *uj) {
  cryptotest_otbn_sca_en_masks_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_en_masks_t(uj, &uj_data));
  if (*uj_data.en_masks) {
    en_masks = true;
  } else {
    en_masks = false;
  }
  return OK_STATUS(0);
}

/**
 * Set seed command handler.
 *
 * The seed must be `kEcc256SeedNumBytes` bytes long.
 *
 * The uJSON data contains:
 *  - seed: Value for seed share.
 *  - seed_len: Length of seed share.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_set_seed(ujson_t *uj) {
  // As receiving 40 bytes over uJSON seems not to work, receive the lower
  // and upper 20 bytes of the seed separately.
  cryptotest_otbn_sca_seed_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_seed_t(uj, &uj_data));

  memcpy(ecc256_seed, uj_data.seed, kEcc256SeedNumBytes);
  // Run PRNG once to synch with capture side. There it is used also to
  // generate the fixed seed.
  uint32_t temp[kEcc256SeedNumWords];
  prng_rand_bytes((unsigned char *)temp, kEcc256SeedNumBytes);
  LOG_ERROR("FIN handle_otbn_sca_ecc256_set_seed");
  return OK_STATUS(0);
}

/**
 * Set constant command handler.
 *
 * The constant must be `kEcc256SeedNumBytes` bytes long.
 *
 * @param C Value of the C constant.
 * @param len Length of the C constant.
 */
status_t handle_otbn_sca_ecc256_set_c(ujson_t *uj) {
  cryptotest_otbn_sca_constant_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_constant_t(uj, &uj_data));
  if (uj_data.constant_len != kEcc256SeedNumBytes) {
    return OUT_OF_RANGE();
  }
  memcpy(ecc256_C, uj_data.constant, uj_data.constant_len);
  return OK_STATUS(0);
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
 */
static ecc256_keygen_sca_error_t p256_run_keygen(uint32_t mode,
                                                 const uint32_t *share0,
                                                 const uint32_t *share1) {
  // Write mode.
  if (otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }

  // Write seed shares.
  if (otbn_dmem_write(kEcc256SeedNumWords, share0, kOtbnVarSeed0).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }
  if (otbn_dmem_write(kEcc256SeedNumWords, share1, kOtbnVarSeed1).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }

  // Execute program.
  sca_set_trigger_high();
  sca_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles);
  otbn_busy_wait_for_done();
  sca_set_trigger_low();

  return ecc256KeygenOk;
}

/**
 * Ecc256 ecdsa keygen fvsr seed batch command handler.
 *
 * The uJSON data contains:
 *  - num_traces: The number of traces.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(ujson_t *uj) {
  cryptotest_otbn_sca_num_traces_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_num_traces_t(uj, &uj_data));

  uint32_t num_traces = 0;
  uint32_t batch_digest[kEcc256SeedNumWords];
  uint8_t dummy[kEcc256SeedNumBytes];
  num_traces = *uj_data.num_traces;

  if (num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // zero the batch digest
  for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
    batch_digest[j] = 0;
  }

  for (uint32_t i = 0; i < num_traces; ++i) {
    if (run_fixed) {
      memcpy(batch_share0[i], ecc256_seed, kEcc256SeedNumBytes);
    } else {
      prng_rand_bytes((unsigned char *)batch_share0[i], kEcc256SeedNumBytes);
    }
    if (en_masks) {
      prng_rand_bytes((unsigned char *)batch_share1[i], kEcc256SeedNumBytes);
    } else {
      for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = 0;
      }
    }
    for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_share0[i][j] ^= batch_share1[i][j];
    }
    // Another PRNG run to determine 'run_fixed' for the next cycle.
    prng_rand_bytes(dummy, kEcc256SeedNumBytes);
    run_fixed = dummy[0] & 0x1;
  }

  for (uint32_t i = 0; i < num_traces; ++i) {
    p256_run_keygen(kEcc256ModePrivateKeyOnly, batch_share0[i],
                    batch_share1[i]);

    // Read results.
    if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0_batch).value !=
        OTCRYPTO_OK.value) {
      return ABORTED();
    }
    if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1_batch).value !=
        OTCRYPTO_OK.value) {
      return ABORTED();
    }

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all d0 shares of
    // the batch.
    for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_digest[j] ^= d0_batch[j];
    }
  }

  // Send the batch digest to the host for verification.
  cryptotest_otbn_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest,
         kEcc256SeedNumWords * 4);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_batch_digest_t, uj, &uj_output);

  return OK_STATUS(0);
}

/**
 * Adds two integers storred in byte arrays.
 *
 * Adds the integer stored in source array to the integer stored in
 * destination aray.
 * The user needs to ensure that dest_len isenough to store the result
 * without overflow.
 *
 * @param[in] dest  Location of the first input array and the result.
 * @param[in] source  Location of the second input array.
 * @param[in] dest_len   Length od the dest array in bytes.
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
 * Ecc256 ecdsa keygen fvsr key batch command handler.
 *
 * The uJSON data contains:
 *  - num_traces: The number of traces.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(ujson_t *uj) {
  cryptotest_otbn_sca_num_traces_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_num_traces_t(uj, &uj_data));

  uint32_t num_traces = 0;
  uint32_t batch_digest[kEcc256SeedNumWords];
  uint8_t dummy[kEcc256SeedNumBytes];
  num_traces = *uj_data.num_traces;

  if (num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // zero the batch digest
  for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
    batch_digest[j] = 0;
  }

  for (uint32_t i = 0; i < num_traces; ++i) {
    if (run_fixed) {
      memcpy(batch_share0[i], ecc256_seed, kEcc256SeedNumBytes);
    } else {
      // Here change to random_number + C
      // It is necessary to set the C first
      memcpy(batch_share0[i], ecc256_C, kEcc256SeedNumBytes);
      prng_rand_bytes((unsigned char *)random_number, kEcc256CoordNumBytes);
      add_arrays((unsigned char *)batch_share0[i],
                 (unsigned char *)random_number, kEcc256SeedNumBytes,
                 kEcc256CoordNumBytes);
    }
    if (en_masks) {
      prng_rand_bytes((unsigned char *)batch_share1[i], kEcc256SeedNumBytes);
    } else {
      for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
        batch_share1[i][j] = 0;
      }
    }
    for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_share0[i][j] ^= batch_share1[i][j];
    }
    // Another PRNG run to determine 'run_fixed' for the next cycle.
    prng_rand_bytes(dummy, kEcc256SeedNumBytes);

    run_fixed = dummy[0] & 0x1;
  }

  for (uint32_t i = 0; i < num_traces; ++i) {
    p256_run_keygen(kEcc256ModePrivateKeyOnly, batch_share0[i],
                    batch_share1[i]);

    // Read results.
    if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0_batch).value !=
        OTCRYPTO_OK.value) {
      return ABORTED();
    }
    if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1_batch).value !=
        OTCRYPTO_OK.value) {
      return ABORTED();
    }

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all d0 shares of
    // the batch.
    for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_digest[j] ^= d0_batch[j];
    }
  }
  // Send the batch digest to the host for verification.
  cryptotest_otbn_sca_batch_digest_t uj_output;
  memcpy(uj_output.batch_digest, (uint8_t *)batch_digest,
         kEcc256SeedNumWords * 4);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_batch_digest_t, uj, &uj_output);

  return OK_STATUS(0);
}

/**
 * Generates a secret key from a masked seed.
 *
 * The seed shares must be `kEcc256SeedNumWords` words long, and the caller
 * must provide pre-allocated buffers of the same length for the private key
 * shares.
 *
 * @param[in] seed  Seed for key generation.
 * @param[in] mask  Mask for seed.
 * @param[out] d0   First share of masked private key d.
 * @param[out] d1   Second share of masked private key d.
 */
static ecc256_keygen_sca_error_t p256_ecdsa_gen_secret_key(const uint32_t *seed,
                                                           const uint32_t *mask,
                                                           uint32_t *d0,
                                                           uint32_t *d1) {
  // Compute first share of seed (seed ^ mask).
  uint32_t share0[kEcc256SeedNumWords];
  for (size_t i = 0; i < kEcc256SeedNumWords; i++) {
    share0[i] = seed[i] ^ mask[i];
  }

  // Run the key generation program.
  p256_run_keygen(kEcc256ModePrivateKeyOnly, share0, mask);

  // Read results.
  if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }
  if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }

  return ecc256KeygenOk;
}

/**
 * Generates a keypair from a masked seed.
 *
 * The seed shares must be `kEcc256SeedNumWords` words long, and the caller
 * must provide pre-allocated buffers of the same length for the private key
 * shares and of length `kEcc256CoordNumWords` for the public key coordinates.
 *
 * @param[in] seed  Seed for key generation.
 * @param[in] mask  Mask for seed.
 * @param[out] d0   First share of masked private key d.
 * @param[out] d1   Second share of masked private key d.
 * @param[out] x    x-coordinate of public key Q.
 * @param[out] y    y-coordinate of public key Q.
 */
static ecc256_keygen_sca_error_t p256_ecdsa_gen_keypair(
    const uint32_t *seed, const uint32_t *mask, uint32_t *d0, uint32_t *d1,
    uint32_t *x, uint32_t *y) {
  // Compute the first share of the seed (seed ^ mask).
  uint32_t share0[kEcc256SeedNumWords];
  for (size_t i = 0; i < kEcc256SeedNumWords; i++) {
    share0[i] = seed[i] ^ mask[i];
  }

  // Run the key generation program.
  p256_run_keygen(kEcc256ModeKeypair, share0, mask);

  // Read results.
  if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }
  if (otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }
  if (otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarX, x).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }
  if (otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarY, y).value !=
      OTCRYPTO_OK.value) {
    return ecc256KeygenAborted;
  }

  return ecc256KeygenOk;
}

/**
 * Ecc256 ecdsa secret keygen command handler.
 *
 * The uJSON data contains:
 *  - mask: The mask.
 *  - mask_len: The mask length.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_ecdsa_secret_keygen(ujson_t *uj) {
  cryptotest_otbn_sca_mask_t uj_data;
  TRY(ujson_deserialize_cryptotest_otbn_sca_mask_t(uj, &uj_data));

  // Copy mask to an aligned buffer.
  uint32_t ecc256_mask[kEcc256SeedNumWords];
  memcpy(ecc256_mask, uj_data.mask, kEcc256SeedNumBytes);

  uint32_t ecc256_d0[kEcc256SeedNumWords];
  uint32_t ecc256_d1[kEcc256SeedNumWords];
  if (p256_ecdsa_gen_secret_key(ecc256_seed, ecc256_mask, ecc256_d0,
                                ecc256_d1) != ecc256KeygenOk) {
    LOG_ERROR("ABORTED");
    return ABORTED();
  }
  cryptotest_otbn_sca_ecc_seed_d0_t uj_output_d0;
  cryptotest_otbn_sca_ecc_seed_d1_t uj_output_d1;

  memcpy(uj_output_d0.d0, (uint8_t *)ecc256_d0, kEcc256SeedNumBytes / 2);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_d0_t, uj, &uj_output_d0);
  memcpy(uj_output_d0.d0, (uint8_t *)ecc256_d0 + kEcc256SeedNumBytes / 2,
         kEcc256SeedNumBytes / 2);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_d0_t, uj, &uj_output_d0);
  memcpy(uj_output_d1.d1, (uint8_t *)ecc256_d1, kEcc256SeedNumBytes / 2);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_d1_t, uj, &uj_output_d1);
  memcpy(uj_output_d1.d1, (uint8_t *)ecc256_d1 + kEcc256SeedNumBytes / 2,
         kEcc256SeedNumBytes / 2);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_d1_t, uj, &uj_output_d1);

  // Uncomment for testing:
  cryptotest_otbn_sca_ecc_seed_t uj_output;
  memcpy(uj_output.d0, (uint8_t *)ecc256_d0, kEcc256SeedNumBytes);
  memcpy(uj_output.d1, (uint8_t *)ecc256_d1, kEcc256SeedNumBytes);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_t, uj, &uj_output);

  return OK_STATUS(0);
}

/**
 * Ecc256 ecdsa gen keypair command handler.
 *
 * The uJSON data contains:
 *  - mask: The mask.
 *  - mask_len: The mask length.
 *
 * @param uj The received uJSON data.
 */
status_t handle_otbn_sca_ecc256_ecdsa_gen_keypair(ujson_t *uj) {
  // As receiving 40 bytes over uJSON seems not to work, receive the lower
  // and upper 20 bytes of the 40 bytes mask separately.
  cryptotest_otbn_sca_mask_t uj_data_l;
  TRY(ujson_deserialize_cryptotest_otbn_sca_mask_t(uj, &uj_data_l));

  cryptotest_otbn_sca_mask_t uj_data_h;
  TRY(ujson_deserialize_cryptotest_otbn_sca_mask_t(uj, &uj_data_h));

  // Copy mask to an aligned buffer.
  uint32_t ecc256_mask[kEcc256SeedNumWords];
  memcpy(ecc256_mask, uj_data_l.mask, kEcc256SeedNumBytes / 2);
  memcpy(ecc256_mask + (kEcc256SeedNumBytes / 2), uj_data_h.mask,
         kEcc256SeedNumBytes / 2);

  uint32_t ecc256_d0[kEcc256SeedNumWords];
  uint32_t ecc256_d1[kEcc256SeedNumWords];
  uint32_t ecc256_x[kEcc256CoordNumWords];
  uint32_t ecc256_y[kEcc256CoordNumWords];
  if (p256_ecdsa_gen_keypair(ecc256_seed, ecc256_mask, ecc256_d0, ecc256_d1,
                             ecc256_x, ecc256_y) != ecc256KeygenOk) {
    return ABORTED();
  }

  /*cryptotest_otbn_sca_ecc_seed_t uj_output_seed;
  memcpy(uj_output_seed.d0, (uint8_t *)ecc256_d0, kEcc256SeedNumBytes);
  memcpy(uj_output_seed.d1, (uint8_t *)ecc256_d1, kEcc256SeedNumBytes);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_seed_t, uj,
  &uj_output_seed);*/

  cryptotest_otbn_sca_ecc_coord_t uj_output_coord;
  memcpy(uj_output_coord.x, (uint8_t *)ecc256_x, kEcc256CoordNumBytes);
  memcpy(uj_output_coord.y, (uint8_t *)ecc256_y, kEcc256CoordNumBytes);
  RESP_OK(ujson_serialize_cryptotest_otbn_sca_ecc_coord_t, uj,
          &uj_output_coord);

  return OK_STATUS(0);
}
