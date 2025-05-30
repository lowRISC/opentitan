// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/otbn_sca.h"

#include "ecc256_keygen_sca.h"
#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

static dif_otbn_t otbn;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

enum {
  kKeySideloadNumIt = 16,
  /**
   * Number of bytes for ECDSA P-256 private keys, message digests, and point
   * coordinates.
   */
  kEcc256NumBytes = 256 / 8,
  /**
   * Number of 32b words for ECDSA P-256 private keys, message digests, and
   * point coordinates.
   */
  kEcc256NumWords = kEcc256NumBytes / sizeof(uint32_t),
  /**
   * Max number of traces per batch.
   */
  kNumBatchOpsMax = 256,
};

// Data structs for key sideloading test.
OTBN_DECLARE_APP_SYMBOLS(otbn_key_sideload_sca);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s0_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s0_h);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s1_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_s1_h);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_l);
OTBN_DECLARE_SYMBOL_ADDR(otbn_key_sideload_sca, k_h);
const otbn_app_t kOtbnAppKeySideloadSca =
    OTBN_APP_T_INIT(otbn_key_sideload_sca);
static const otbn_addr_t kOtbnAppKeySideloadks0l =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s0_l);
static const otbn_addr_t kOtbnAppKeySideloadks0h =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s0_h);
static const otbn_addr_t kOtbnAppKeySideloadks1l =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s1_l);
static const otbn_addr_t kOtbnAppKeySideloadks1h =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_s1_h);
static const otbn_addr_t kOtbnAppKeySideloadkl =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_l);
static const otbn_addr_t kOtbnAppKeySideloadkh =
    OTBN_ADDR_T_INIT(otbn_key_sideload_sca, k_h);

// RSA OTBN App.
OTBN_DECLARE_APP_SYMBOLS(rsa);
OTBN_DECLARE_SYMBOL_ADDR(rsa, mode);
OTBN_DECLARE_SYMBOL_ADDR(rsa, n_limbs);
OTBN_DECLARE_SYMBOL_ADDR(rsa, inout);
OTBN_DECLARE_SYMBOL_ADDR(rsa, modulus);
OTBN_DECLARE_SYMBOL_ADDR(rsa, exp);

static const otbn_app_t kOtbnAppRsa = OTBN_APP_T_INIT(rsa);
static const otbn_addr_t kOtbnVarRsaMode = OTBN_ADDR_T_INIT(rsa, mode);
static const otbn_addr_t kOtbnVarRsaNLimbs = OTBN_ADDR_T_INIT(rsa, n_limbs);
static const otbn_addr_t kOtbnVarRsaInOut = OTBN_ADDR_T_INIT(rsa, inout);
static const otbn_addr_t kOtbnVarRsaModulus = OTBN_ADDR_T_INIT(rsa, modulus);
static const otbn_addr_t kOtbnVarRsaExp = OTBN_ADDR_T_INIT(rsa, exp);

// p256_ecdsa_sca has randomization removed.
OTBN_DECLARE_APP_SYMBOLS(p256_ecdsa_sca);

OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, mode);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, msg);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, r);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, s);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, x);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, y);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, d0);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, d1);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, k0);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, k1);
OTBN_DECLARE_SYMBOL_ADDR(p256_ecdsa_sca, x_r);

static const otbn_app_t kOtbnAppP256Ecdsa = OTBN_APP_T_INIT(p256_ecdsa_sca);

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(p256_ecdsa_sca, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(p256_ecdsa_sca, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(p256_ecdsa_sca, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(p256_ecdsa_sca, s);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, d0);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, d1);
static const otbn_addr_t kOtbnVarK0 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, k0);
static const otbn_addr_t kOtbnVarK1 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, k1);

/**
 * Clears the OTBN DMEM and IMEM.
 *
 * @returns OK or error.
 */
static status_t clear_otbn(void) {
  // Clear OTBN memory.
  TRY(otbn_dmem_sec_wipe());
  TRY(otbn_imem_sec_wipe());

  return OK_STATUS();
}

/**
 * Generate masked shared.
 *
 * If mask_en is set, generate a random share.
 * If mask_en is not set, set share to 0.
 *
 * @param dest_array          Destination array.
 * @param mask_en             Masking enabled or disabled.
 * @param len                 Length of the array.
 */
void gen_mask_data(uint32_t *dest_array, bool mask_en, size_t len) {
  if (mask_en) {
    for (size_t j = 0; j < len; ++j) {
      dest_array[j] = prng_rand_uint32();
    }
  } else {
    memset(dest_array, 0, len * sizeof(dest_array[0]));
  }
}

/**
 * Generate a FvsR data set.
 *
 * If fixed is set, copy src_fixed_array into dest_array.
 * If fixed is not set, generate random data.
 *
 * @param dest_array          Destination array.
 * @param fixed               Fixed or random set.
 * @param src_fixed_array     Source fixed array.
 * @param len                 Length of the array.
 */
void gen_fvsr_data(uint32_t *dest_array, bool fixed, uint32_t *src_fixed_array,
                   size_t len) {
  if (fixed) {
    memcpy(dest_array, src_fixed_array, len * sizeof(src_fixed_array[0]));
  } else {
    for (size_t j = 0; j < len; ++j) {
      dest_array[j] = prng_rand_uint32();
    }
  }
}

/**
 * Signs a message with ECDSA using the P-256 curve.
 *
 * R = k*G
 * r = x-coordinate of R
 * s = k^(-1)(msg + r*d)  mod n
 *
 * @param otbn_ctx            The OTBN context object.
 * @param msg                 The message to sign, msg (32B).
 * @param private_key_d       The private key, d (32B).
 * @param k                   The ephemeral key,  k (random scalar) (32B).
 * @param[out] signature_r    Signature component r (the x-coordinate of R).
 *                            Provide a pre-allocated 32B buffer.
 * @param[out] signature_s    Signature component s (the proof).
 *                            Provide a pre-allocated 32B buffer.
 */
static status_t p256_ecdsa_sign(const uint32_t *msg,
                                const uint32_t *private_key_d,
                                uint32_t *signature_r, uint32_t *signature_s,
                                const uint32_t *k) {
  uint32_t mode = 1;  // mode 1 => sign
  // Send operation mode to OTBN
  TRY(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode));
  // Send Msg to OTBN
  TRY(otbn_dmem_write(kEcc256NumWords, msg, kOtbnVarMsg));
  // Send two shares of private_key_d to OTBN
  TRY(otbn_dmem_write(kEcc256NumWords, private_key_d, kOtbnVarD0));
  TRY(otbn_dmem_write(kEcc256NumWords, private_key_d + kEcc256NumWords,
                      kOtbnVarD1));
  // Send two shares of secret_k to OTBN
  TRY(otbn_dmem_write(kEcc256NumWords, k, kOtbnVarK0));
  TRY(otbn_dmem_write(kEcc256NumWords, k + kEcc256NumWords, kOtbnVarK1));

  // Start OTBN execution
  pentest_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Read the results back (sig_r, sig_s)
  TRY(otbn_dmem_read(kEcc256NumWords, kOtbnVarR, signature_r));
  TRY(otbn_dmem_read(kEcc256NumWords, kOtbnVarS, signature_s));

  return OK_STATUS();
}

status_t handle_otbn_sca_ecdsa_p256_sign(ujson_t *uj) {
  // Get masks off or on.
  penetrationtest_otbn_sca_en_masks_t uj_data_masks;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_en_masks_t(uj,
                                                            &uj_data_masks));

  // Get message and key.
  penetrationtest_otbn_sca_ecdsa_p256_sign_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_ecdsa_p256_sign_t(uj,
                                                                   &uj_data));

  // Set of share d1 for masking.
  uint32_t ecc256_private_key_d1[kEcc256NumWords];
  memset(ecc256_private_key_d1, 0, sizeof(ecc256_private_key_d1));
  // If masking is activated, generate random share d1.
  if (uj_data_masks.en_masks) {
    for (size_t j = 0; j < kEcc256NumWords; j++) {
      ecc256_private_key_d1[j] = prng_rand_uint32();
    }
  }

  // Set of share k1 for masking.
  uint32_t ecc256_secret_k1[kEcc256NumWords];
  memset(ecc256_secret_k1, 0, sizeof(ecc256_secret_k1));
  // If masking is activated, generate random share d1.
  if (uj_data_masks.en_masks) {
    for (size_t j = 0; j < kEcc256NumWords; j++) {
      ecc256_secret_k1[j] = prng_rand_uint32();
    }
  }

  // Combine D0 and D1 into the private key.
  uint32_t ecc256_private_key_d[2 * kEcc256NumWords];
  memset(ecc256_private_key_d, 0, sizeof(ecc256_private_key_d));
  memcpy(ecc256_private_key_d, uj_data.d0, sizeof(uj_data.d0));
  memcpy(ecc256_private_key_d + kEcc256NumWords, ecc256_private_key_d1,
         sizeof(ecc256_private_key_d1));

  // Combine K0 and K1 into the secret key.
  uint32_t ecc256_secret_k[2 * kEcc256NumWords];
  memset(ecc256_secret_k, 0, sizeof(ecc256_secret_k));
  memcpy(ecc256_secret_k, uj_data.k0, sizeof(uj_data.k0));
  memcpy(ecc256_secret_k + kEcc256NumWords, ecc256_secret_k1,
         sizeof(ecc256_secret_k1));

  otbn_load_app(kOtbnAppP256Ecdsa);

  // Signature output.
  uint32_t ecc256_signature_r[kEcc256NumWords];
  uint32_t ecc256_signature_s[kEcc256NumWords];

  // Start the operation.
  p256_ecdsa_sign(uj_data.msg, ecc256_private_key_d, ecc256_signature_r,
                  ecc256_signature_s, ecc256_secret_k);

  // Send back signature to host.
  penetrationtest_otbn_sca_ecdsa_p256_signature_t uj_output;
  memcpy(uj_output.r, ecc256_signature_r, sizeof(ecc256_signature_r));
  memcpy(uj_output.s, ecc256_signature_s, sizeof(ecc256_signature_s));
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_ecdsa_p256_signature_t, uj,
          &uj_output);

  // Clear OTBN memory
  TRY(clear_otbn());

  return OK_STATUS();
}

status_t handle_otbn_sca_ecdsa_p256_sign_batch(ujson_t *uj) {
  // Get number of traces.
  penetrationtest_otbn_sca_num_traces_t uj_data_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(
      uj, &uj_data_num_traces));

  if (uj_data_num_traces.num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // Get masks off or on.
  penetrationtest_otbn_sca_en_masks_t uj_data_masks;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_en_masks_t(uj,
                                                            &uj_data_masks));

  // Create random message, k, and d.
  uint32_t ecc256_message_batch[kNumBatchOpsMax][kEcc256NumWords];

  uint32_t ecc256_private_key_d0_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_private_key_d1_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_private_key_d_batch[kNumBatchOpsMax][2 * kEcc256NumWords];

  uint32_t ecc256_secret_key_k0_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_secret_key_k1_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_secret_key_k_batch[kNumBatchOpsMax][2 * kEcc256NumWords];

  // Generate the FvsR data set.
  for (size_t i = 0; i < uj_data_num_traces.num_traces; ++i) {
    // Generate random message.
    gen_fvsr_data(ecc256_message_batch[i], false, NULL, kEcc256NumWords);

    // Set random private key d0.
    gen_fvsr_data(ecc256_private_key_d0_batch[i], false, NULL, kEcc256NumWords);

    // When masks are on, set random private key d1. If masks are off, set to 0.
    gen_mask_data(ecc256_private_key_d1_batch[i], uj_data_masks.en_masks,
                  kEcc256NumWords);

    // Combine both shares d0 and d1 to d.
    memcpy(ecc256_private_key_d_batch[i], ecc256_private_key_d0_batch[i],
           sizeof(ecc256_private_key_d0_batch[i]));
    memcpy(ecc256_private_key_d_batch[i] + kEcc256NumWords,
           ecc256_private_key_d1_batch[i],
           sizeof(ecc256_private_key_d1_batch[i]));

    // Set random secret key k0.
    gen_fvsr_data(ecc256_secret_key_k0_batch[i], false, NULL, kEcc256NumWords);

    // When masks are on, set random secret key k1. If masks are off, set to 0.
    gen_mask_data(ecc256_secret_key_k1_batch[i], uj_data_masks.en_masks,
                  kEcc256NumWords);

    // Combine both shares k0 and k1 to k.
    memcpy(ecc256_secret_key_k_batch[i], ecc256_secret_key_k0_batch[i],
           sizeof(ecc256_secret_key_k0_batch[i]));
    memcpy(ecc256_secret_key_k_batch[i] + kEcc256NumWords,
           ecc256_secret_key_k1_batch[i],
           sizeof(ecc256_secret_key_k1_batch[i]));
  }

  // Last signature output.
  uint32_t ecc256_signature_r[kEcc256NumWords];
  uint32_t ecc256_signature_s[kEcc256NumWords];
  // Run num_traces ECDSA operations.
  for (size_t i = 0; i < uj_data_num_traces.num_traces; ++i) {
    otbn_load_app(kOtbnAppP256Ecdsa);

    // Start the operation.
    p256_ecdsa_sign(ecc256_message_batch[i], ecc256_private_key_d_batch[i],
                    ecc256_signature_r, ecc256_signature_s,
                    ecc256_secret_key_k_batch[i]);
  }

  // Send back the last signature to host.
  penetrationtest_otbn_sca_ecdsa_p256_signature_t uj_output;
  memcpy(uj_output.r, ecc256_signature_r, sizeof(ecc256_signature_r));
  memcpy(uj_output.s, ecc256_signature_s, sizeof(ecc256_signature_s));
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_ecdsa_p256_signature_t, uj,
          &uj_output);

  // Clear OTBN memory
  TRY(clear_otbn());

  return OK_STATUS();
}

status_t handle_otbn_sca_ecdsa_p256_sign_fvsr_batch(ujson_t *uj) {
  // Get number of traces.
  penetrationtest_otbn_sca_num_traces_t uj_data_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(
      uj, &uj_data_num_traces));

  if (uj_data_num_traces.num_traces > kNumBatchOpsMax) {
    return OUT_OF_RANGE();
  }

  // Get masks off or on.
  penetrationtest_otbn_sca_en_masks_t uj_data_masks;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_en_masks_t(uj,
                                                            &uj_data_masks));

  // Get fixed message and key.
  penetrationtest_otbn_sca_ecdsa_p256_sign_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_ecdsa_p256_sign_t(uj,
                                                                   &uj_data));

  uint32_t ecc256_message_batch[kNumBatchOpsMax][kEcc256NumWords];

  uint32_t ecc256_private_key_d0_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_private_key_d1_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_private_key_d_batch[kNumBatchOpsMax][2 * kEcc256NumWords];

  uint32_t ecc256_secret_key_k0_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_secret_key_k1_batch[kNumBatchOpsMax][kEcc256NumWords];
  uint32_t ecc256_secret_key_k_batch[kNumBatchOpsMax][2 * kEcc256NumWords];

  // Generate the FvsR data set. For each trace, message, k, and d is either set
  // to fixed received from the host over uJSON or random.
  bool run_fixed = true;
  for (size_t i = 0; i < uj_data_num_traces.num_traces; ++i) {
    // Set message.
    gen_fvsr_data(ecc256_message_batch[i], run_fixed, uj_data.msg,
                  kEcc256NumWords);

    // If the run is fixed, take the private key received over uJSON. Else,
    // generate a random private key.
    gen_fvsr_data(ecc256_private_key_d0_batch[i], run_fixed, uj_data.d0,
                  kEcc256NumWords);

    // When masks are on, set fixed or random private key d1. If masks are off,
    // set to 0.
    gen_mask_data(ecc256_private_key_d1_batch[i], uj_data_masks.en_masks,
                  kEcc256NumWords);

    // Combine both shares
    memcpy(ecc256_private_key_d_batch[i], ecc256_private_key_d0_batch[i],
           sizeof(ecc256_private_key_d0_batch[i]));
    memcpy(ecc256_private_key_d_batch[i] + kEcc256NumWords,
           ecc256_private_key_d1_batch[i],
           sizeof(ecc256_private_key_d1_batch[i]));

    // Set random secret key k0.
    // If the run is fixed, take the private key received over uJSON. Else,
    // generate a random private key.
    gen_fvsr_data(ecc256_secret_key_k0_batch[i], run_fixed, uj_data.k0,
                  kEcc256NumWords);

    // When masks are on, set random secret key k1. If masks are off, set to 0.
    gen_mask_data(ecc256_secret_key_k1_batch[i], uj_data_masks.en_masks,
                  kEcc256NumWords);

    // Combine both shares k0 and k1 to k.
    memcpy(ecc256_secret_key_k_batch[i], ecc256_secret_key_k0_batch[i],
           sizeof(ecc256_secret_key_k0_batch[i]));
    memcpy(ecc256_secret_key_k_batch[i] + kEcc256NumWords,
           ecc256_secret_key_k1_batch[i],
           sizeof(ecc256_secret_key_k1_batch[i]));

    run_fixed = prng_rand_uint32() & 0x1;
  }

  // Last signature output.
  uint32_t ecc256_signature_r[kEcc256NumWords];
  uint32_t ecc256_signature_s[kEcc256NumWords];
  // Run num_traces ECDSA operations.
  for (size_t i = 0; i < uj_data_num_traces.num_traces; ++i) {
    otbn_load_app(kOtbnAppP256Ecdsa);

    // Start the operation.
    p256_ecdsa_sign(uj_data.msg, ecc256_private_key_d_batch[i],
                    ecc256_signature_r, ecc256_signature_s,
                    ecc256_secret_key_k_batch[i]);
  }

  // Send back the last signature to host.
  penetrationtest_otbn_sca_ecdsa_p256_signature_t uj_output;
  memcpy(uj_output.r, ecc256_signature_r, sizeof(ecc256_signature_r));
  memcpy(uj_output.s, ecc256_signature_s, sizeof(ecc256_signature_s));
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_ecdsa_p256_signature_t, uj,
          &uj_output);

  // Clear OTBN memory
  TRY(clear_otbn());

  return OK_STATUS();
}

status_t handle_otbn_pentest_init(ujson_t *uj) {
  penetrationtest_cpuctrl_t uj_data;
  TRY(ujson_deserialize_penetrationtest_cpuctrl_t(uj, &uj_data));

  // Configure the entropy complex for OTBN. Set the reseed interval to max
  // to avoid a non-constant trigger window.
  TRY(pentest_configure_entropy_source_max_reseed_interval());

  pentest_init(kPentestTriggerSourceOtbn,
               kPentestPeripheralEntropy | kPentestPeripheralIoDiv4 |
                   kPentestPeripheralOtbn | kPentestPeripheralCsrng |
                   kPentestPeripheralEdn | kPentestPeripheralHmac |
                   kPentestPeripheralKmac);

  // Init the OTBN core.
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Load p256 keygen from seed app into OTBN.
  if (otbn_load_app(kOtbnAppP256KeyFromSeed).value != OTCRYPTO_OK.value) {
    return ABORTED();
  }

  // Configure the CPU for the pentest.
  penetrationtest_device_info_t uj_output;
  TRY(pentest_configure_cpu(
      uj_data.icache_disable, uj_data.dummy_instr_disable,
      uj_data.enable_jittery_clock, uj_data.enable_sram_readback,
      &uj_output.clock_jitter_locked, &uj_output.clock_jitter_en,
      &uj_output.sram_main_readback_locked, &uj_output.sram_ret_readback_locked,
      &uj_output.sram_main_readback_en, &uj_output.sram_ret_readback_en));

  // Read device ID and return to host.
  TRY(pentest_read_device_id(uj_output.device_id));
  RESP_OK(ujson_serialize_penetrationtest_device_info_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_pentest_init_keymgr(ujson_t *uj) {
  if (kBootStage != kBootStageOwner) {
    TRY(keymgr_testutils_startup(&keymgr, &kmac));
    // Advance to OwnerIntermediateKey state.
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
    TRY(keymgr_testutils_check_state(&keymgr,
                                     kDifKeymgrStateOwnerIntermediateKey));
    LOG_INFO("Keymgr entered OwnerIntKey State");
  } else {
    TRY(dif_keymgr_init(mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR),
                        &keymgr));
    TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));
  }

  dif_otbn_t otbn;
  TRY(dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  return OK_STATUS();
}

status_t handle_otbn_sca_insn_carry_flag(ujson_t *uj) {
  // Get big number (256 bit).
  penetrationtest_otbn_sca_big_num_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_big_num_t(uj, &uj_data));

  // INSN Carry Flag OTBN App.
  OTBN_DECLARE_APP_SYMBOLS(otbn_insn_carry_flag);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_insn_carry_flag, big_num);
  OTBN_DECLARE_SYMBOL_ADDR(otbn_insn_carry_flag, big_num_out);

  static const otbn_app_t kOtbnAppInsnCarryFlag =
      OTBN_APP_T_INIT(otbn_insn_carry_flag);
  static const otbn_addr_t kOtbnVarInsnCarryFlagBigNum =
      OTBN_ADDR_T_INIT(otbn_insn_carry_flag, big_num);
  static const otbn_addr_t kOtbnVarInsnCarryFlagBigNumOut =
      OTBN_ADDR_T_INIT(otbn_insn_carry_flag, big_num_out);

  // Load app and write received big_num into DMEM.
  otbn_load_app(kOtbnAppInsnCarryFlag);
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarInsnCarryFlagBigNum, uj_data.big_num,
                          sizeof(uj_data.big_num)));

  pentest_set_trigger_high();
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  penetrationtest_otbn_sca_big_num_t uj_output;
  memset(uj_output.big_num, 0, sizeof(uj_output.big_num));
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarInsnCarryFlagBigNumOut,
                         uj_output.big_num, sizeof(uj_output.big_num)));

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_big_num_t, uj, &uj_output);

  return OK_STATUS();
}

status_t handle_otbn_sca_key_sideload_fvsr(ujson_t *uj) {
  // Get fixed seed.
  penetrationtest_otbn_sca_fixed_seed_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_fixed_seed_t(uj, &uj_data));

  // Key generation parameters.
  dif_keymgr_versioned_key_params_t sideload_params[kKeySideloadNumIt];

  // Generate FvsR values.
  bool sample_fixed = true;
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    sideload_params[it].version = 0x0;
    sideload_params[it].dest = kDifKeymgrVersionedKeyDestOtbn;
    memset(sideload_params[it].salt, 0, sizeof(sideload_params[it].salt));
    if (sample_fixed) {
      sideload_params[it].salt[0] = uj_data.fixed_seed;
    } else {
      sideload_params[it].salt[0] = prng_rand_uint32();
    }
    sample_fixed = prng_rand_uint32() & 0x1;
  }

  otbn_load_app(kOtbnAppKeySideloadSca);

  uint32_t key_share_0_l[kKeySideloadNumIt], key_share_0_h[kKeySideloadNumIt];
  uint32_t key_share_1_l[16], key_share_1_h[kKeySideloadNumIt];
  uint32_t key_l[kKeySideloadNumIt], key_h[kKeySideloadNumIt];

  // SCA code target.
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    TRY(keymgr_testutils_generate_versioned_key(&keymgr, sideload_params[it]));

    TRY(dif_otbn_set_ctrl_software_errs_fatal(&otbn, /*enable=*/false));

    pentest_set_trigger_high();
    // Give the trigger time to rise.
    asm volatile(NOP30);
    otbn_execute();
    otbn_busy_wait_for_done();
    pentest_set_trigger_low();
    asm volatile(NOP30);

    otbn_dmem_read(1, kOtbnAppKeySideloadks0l, &key_share_0_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks0h, &key_share_0_h[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1l, &key_share_1_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadks1h, &key_share_1_h[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadkl, &key_l[it]);
    otbn_dmem_read(1, kOtbnAppKeySideloadkh, &key_h[it]);
  }

  // Write back shares and keys to host.
  penetrationtest_otbn_sca_key_t uj_output;
  for (size_t it = 0; it < kKeySideloadNumIt; it++) {
    uj_output.shares[0] = key_share_0_l[it];
    uj_output.shares[1] = key_share_0_h[it];
    uj_output.shares[2] = key_share_1_l[it];
    uj_output.shares[3] = key_share_1_h[it];
    uj_output.keys[0] = key_l[it];
    uj_output.keys[1] = key_h[it];
    RESP_OK(ujson_serialize_penetrationtest_otbn_sca_key_t, uj, &uj_output);
  }

  return OK_STATUS();
}

status_t handle_otbn_sca_rsa512_decrypt(ujson_t *uj) {
  // Get RSA256 parameters.
  penetrationtest_otbn_sca_rsa512_dec_t uj_data;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_rsa512_dec_t(uj, &uj_data));
  otbn_load_app(kOtbnAppRsa);

  uint32_t mode = 2;  // Decrypt.
  // RSA512 configuration.
  uint32_t n_limbs = 2;

  // Write data into OTBN DMEM.
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaMode, &mode, sizeof(mode)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaNLimbs, &n_limbs, sizeof(n_limbs)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaModulus, uj_data.modu,
                          sizeof(uj_data.modu)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaExp, uj_data.exp,
                          sizeof(uj_data.exp)));
  TRY(dif_otbn_dmem_write(&otbn, kOtbnVarRsaInOut, uj_data.msg,
                          sizeof(uj_data.msg)));

  pentest_set_trigger_high();
  // Give the trigger time to rise.
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  // Send back decryption result to host.
  penetrationtest_otbn_sca_rsa512_dec_out_t uj_output;
  TRY(dif_otbn_dmem_read(&otbn, kOtbnVarRsaInOut, uj_output.out,
                         sizeof(uj_output.out)));
  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_rsa512_dec_out_t, uj,
          &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca(ujson_t *uj) {
  otbn_sca_subcommand_t cmd;
  TRY(ujson_deserialize_otbn_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrKeyBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_key_batch(uj);
    case kOtbnScaSubcommandEcc256EcdsaKeygenFvsrSeedBatch:
      return handle_otbn_sca_ecc256_ecdsa_keygen_fvsr_seed_batch(uj);
    case kOtbnScaSubcommandEcc256EnMasks:
      return handle_otbn_sca_ecc256_en_masks(uj);
    case kOtbnScaSubcommandEcc256SetC:
      return handle_otbn_sca_ecc256_set_c(uj);
    case kOtbnScaSubcommandEcc256SetSeed:
      return handle_otbn_sca_ecc256_set_seed(uj);
    case kOtbnScaSubcommandEcdsaP256Sign:
      return handle_otbn_sca_ecdsa_p256_sign(uj);
    case kOtbnScaSubcommandEcdsaP256SignBatch:
      return handle_otbn_sca_ecdsa_p256_sign_batch(uj);
    case kOtbnScaSubcommandEcdsaP256SignFvsrBatch:
      return handle_otbn_sca_ecdsa_p256_sign_fvsr_batch(uj);
    case kOtbnScaSubcommandInit:
      return handle_otbn_pentest_init(uj);
    case kOtbnScaSubcommandInitKeyMgr:
      return handle_otbn_pentest_init_keymgr(uj);
    case kOtbnScaSubcommandInsnCarryFlag:
      return handle_otbn_sca_insn_carry_flag(uj);
    case kOtbnScaSubcommandKeySideloadFvsr:
      return handle_otbn_sca_key_sideload_fvsr(uj);
    case kOtbnScaSubcommandRsa512Decrypt:
      return handle_otbn_sca_rsa512_decrypt(uj);
    default:
      LOG_ERROR("Unrecognized OTBN SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
