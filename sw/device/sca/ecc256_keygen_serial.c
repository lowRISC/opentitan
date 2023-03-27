// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"

/**
 * OpenTitan program for OTBN ECDSA-P256 side-channel analysis.
 *
 * This program implements the following simple serial commands:
 *   - Set seed ('x'),
 *   - Secret key generation ('k'),
 *   - Keypair generation ('p'),
 *   - Get version ('v') (implemented in simpleserial library),
 *   - Seed PRNG ('s') (implemented in simpleserial library),
 * See https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

OTTF_DEFINE_TEST_CONFIG();

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
  /**
   * Number of bytes for ECDSA P-256 modular inverse input shares (k0,k1).
   */
  kEcc256ModInvInputShareNumBytes = 320 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse input shares (k0,k1).
   */
  kEcc256ModInvInputShareNumWords =
      kEcc256ModInvInputShareNumBytes / sizeof(uint32_t),
  /**
   * Number of bytes for ECDSA P-256 modular inverse output ((k*alpha)^-1 mod
   * n).
   */
  kEcc256ModInvOutputKAlphaInvNumBytes = 256 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse output ((k*alpha)^-1 mod
   * n).
   */
  kEcc256ModInvOutputKAlphaInvNumWords =
      kEcc256ModInvOutputKAlphaInvNumBytes / sizeof(uint32_t),
  /**
   * Number of bytes for ECDSA P-256 modular inverse output mask (alpha).
   */
  kEcc256ModInvOutputAlphaNumBytes = 128 / 8,
  /**
   * Number of words for ECDSA P-256 modular inverse output mask (alpha).
   */
  kEcc256ModInvOutputAlphaNumWords =
      kEcc256ModInvOutputAlphaNumBytes / sizeof(uint32_t),
};

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
 * App configuration for p256_key_from_seed_sca
 */
OTBN_DECLARE_APP_SYMBOLS(p256_key_from_seed_sca);

OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, mode);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, seed0);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, seed1);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, d0);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, d1);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, x);
OTBN_DECLARE_SYMBOL_ADDR(p256_key_from_seed_sca, y);

static const otbn_app_t kOtbnAppP256KeyFromSeed =
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
 * App configuration for p256_mod_inv_sca
 */
OTBN_DECLARE_APP_SYMBOLS(p256_mod_inv_sca);

OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, k0);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, k1);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, kalpha_inv);
OTBN_DECLARE_SYMBOL_ADDR(p256_mod_inv_sca, alpha);

static const otbn_app_t kOtbnAppP256ModInv = OTBN_APP_T_INIT(p256_mod_inv_sca);

static const otbn_addr_t kOtbnVarModInvK0 =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, k0);
static const otbn_addr_t kOtbnVarModInvK1 =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, k1);
static const otbn_addr_t kOtbnVarModInvKAplhaInv =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, kalpha_inv);
static const otbn_addr_t kOtbnVarModInvAlpha =
    OTBN_ADDR_T_INIT(p256_mod_inv_sca, alpha);

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

/**
 * Modular inverse input share values.
 *
 * The default value corresponds to the default values in
 *   sw/otbn/crypto/p256_mod_inv_sca.s
 *
 * These default values can be overwritten via the simpleserial command `i`
 */
uint32_t ecc256_modinv_k0[kEcc256ModInvInputShareNumWords] = {
    0x2130fb63, 0xd47c4a89, 0xcdf7c706, 0x3a27d1b2, 0x210904c7,
    0xbead5ed1, 0xc0fe2d66, 0x2c8d5cd1, 0xf9bb7401, 0x7e8bb020,
};
uint32_t ecc256_modinv_k1[kEcc256ModInvInputShareNumWords] = {
    0x381ea73e, 0x0b02ae2e, 0xf965aef6, 0x2c230bf7, 0x0bf8f151,
    0xde11e80c, 0x87b8dbdd, 0xf9bb7400, 0x06448bff, 0x81744fde,
};

/**
 * Simple serial 'a' (app select) command handler.
 *
 * This handler has to be called to load a new app to otbn.
 *
 * @param app_cmd 0 => ecc256 keygen, 1 => ecc256 modular inverse.
 * @param app_cmd_len Length of sent command value.
 */
static void ecc256_app_select(const uint8_t *app_cmd, size_t app_cmd_len) {
  SS_CHECK(app_cmd_len == 1);
  if (*app_cmd == 0) {
    // wipe otbn memory before loading new app
    otbn_imem_sec_wipe();
    otbn_dmem_sec_wipe();
    // load keygen app
    SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256KeyFromSeed));
  } else if (*app_cmd == 1) {
    // wipe otbn memory before loading new app
    otbn_imem_sec_wipe();
    otbn_dmem_sec_wipe();
    // load mod inv app
    SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256ModInv));
  } else {
    LOG_ERROR("Wrong app select command.");
  }
}

/**
 * Simple serial 'm' (set masks enable) command handler.
 *
 * This can be used for batch mode.
 *
 * @param enable 1 => masks enabled, 0 => masks disabled.
 * @param enable_len Length of sent enable value.
 */
static void ecc256_en_masks(const uint8_t *enable, size_t enable_len) {
  SS_CHECK(enable_len == 1);
  if (*enable) {
    en_masks = true;
  } else {
    en_masks = false;
  }
}

/**
 * Simple serial 'x' (set seed) command handler.
 *
 * The seed must be `kEcc256SeedNumBytes` bytes long.
 *
 * @param seed Value for seed share.
 * @param seed_len Length of seed share.
 */
static void ecc256_set_seed(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == kEcc256SeedNumBytes);
  memcpy(ecc256_seed, seed, seed_len);
}

/**
 * Simple serial 'i' (set modinv k0/k1 input) command handler.
 *
 * Each share must be `kEcc256ModInvInputShareNumBytes` bytes long.
 *
 * @param k0_k1 Value for input.
 * @param k0_k1_len Length of input.
 */
static void ecc256_modinv_set_input(const uint8_t *k0_k1, size_t k0_k1_len) {
  SS_CHECK(k0_k1_len == 2 * kEcc256ModInvInputShareNumBytes);
  // copy k0
  memcpy(ecc256_modinv_k0, k0_k1, kEcc256ModInvInputShareNumBytes);
  // copy k1
  memcpy(ecc256_modinv_k1, (k0_k1 + kEcc256ModInvInputShareNumBytes),
         kEcc256ModInvInputShareNumBytes);
}

/**
 * Callback wrapper for OTBN manual trigger function.
 */
static void otbn_manual_trigger(void) { SS_CHECK_STATUS_OK(otbn_execute()); }

/**
 * Runs the OTBN modular inverse program.
 *
 * The input must be `kEcc256ModInvInputShareNumWords` words long.
 *
 * @param[in] input  Iput value for the OTBN modular inverse.
 */
static void p256_run_modinv(uint32_t *k0, uint32_t *k1) {
  // Write input.
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256ModInvInputShareNumWords, k0, kOtbnVarModInvK0));
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256ModInvInputShareNumWords, k1, kOtbnVarModInvK1));

  // Execute program.
  sca_set_trigger_high();
  sca_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles);
  otbn_busy_wait_for_done();
  sca_set_trigger_low();
}

/**
 * Computes the modular inverse of a certain input.
 *
 * The input must be `kEcc256ModInvInputShareNumWords` words long.
 *
 * @param[in] input  Input for modular inverse computation.
 */
static void ecc256_modinv(const uint8_t *k0_k1, size_t k0_k1_len) {
  if (k0_k1_len != 2 * kEcc256ModInvInputShareNumBytes) {
    LOG_ERROR("Invalid input length %hu", (uint8_t)k0_k1_len);
    return;
  }

  // Copy input to an aligned buffer.
  uint32_t modinv_k0[kEcc256ModInvInputShareNumWords];
  uint32_t modinv_k1[kEcc256ModInvInputShareNumWords];
  memcpy(modinv_k0, k0_k1, kEcc256ModInvInputShareNumBytes);
  memcpy(modinv_k1, (k0_k1 + kEcc256ModInvInputShareNumBytes),
         kEcc256ModInvInputShareNumBytes);

  // Run the key generation program.
  p256_run_modinv(modinv_k0, modinv_k1);

  // Read result.
  uint32_t modinv_kalpha_inv[kEcc256ModInvOutputKAlphaInvNumWords];
  uint32_t modinv_alpha[kEcc256ModInvOutputAlphaNumWords];
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256ModInvOutputKAlphaInvNumWords,
                                    kOtbnVarModInvKAplhaInv,
                                    modinv_kalpha_inv));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256ModInvOutputAlphaNumWords,
                                    kOtbnVarModInvAlpha, modinv_alpha));

  simple_serial_send_packet('r', (unsigned char *)modinv_kalpha_inv,
                            kEcc256ModInvOutputKAlphaInvNumBytes);
  simple_serial_send_packet('r', (unsigned char *)modinv_alpha,
                            kEcc256ModInvOutputAlphaNumBytes);
}

/**
 * Runs the OTBN key generation program.
 *
 * The seed shares must be `kEcc256SeedNumWords` words long.
 *
 * @param[in] mode  Mode parameter (private key only or full keypair).
 * @param[in] seed  Seed for key generation.
 * @param[in] mask  Mask for seed.
 */
static void p256_run_keygen(uint32_t mode, const uint32_t *share0,
                            const uint32_t *share1) {
  // Write mode.
  SS_CHECK_STATUS_OK(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode));

  // Write seed shares.
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256SeedNumWords, share0, kOtbnVarSeed0));
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256SeedNumWords, share1, kOtbnVarSeed1));

  // Execute program.
  sca_set_trigger_high();
  sca_call_and_sleep(otbn_manual_trigger, kIbexOtbnSleepCycles);
  SS_CHECK_STATUS_OK(otbn_busy_wait_for_done());
  sca_set_trigger_low();
}

static void ecc256_ecdsa_secret_keygen_batch(const uint8_t *data,
                                             size_t data_len) {
  uint32_t num_traces = 0;
  uint32_t out[kEcc256SeedNumWords];
  uint32_t batch_digest[kEcc256SeedNumWords];
  uint8_t dummy[kEcc256SeedNumBytes];
  SS_CHECK(data_len == sizeof(num_traces));
  num_traces = read_32(data);

  if (num_traces > kNumBatchOpsMax) {
    LOG_ERROR("Too many traces for one batch.");
    return;
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
    SS_CHECK_STATUS_OK(
        otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0_batch));
    SS_CHECK_STATUS_OK(
        otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1_batch));

    // The correctness of each batch is verified by computing and sending
    // the batch digest. This digest is computed by XORing all d0 shares of
    // the batch.
    for (uint32_t j = 0; j < kEcc256SeedNumWords; ++j) {
      batch_digest[j] ^= d0_batch[j];
    }
  }

  // Send the batch digest to the host for verification.
  simple_serial_send_packet('r', (uint8_t *)batch_digest,
                            kEcc256SeedNumWords * 4);
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
static void p256_ecdsa_gen_secret_key(const uint32_t *seed,
                                      const uint32_t *mask, uint32_t *d0,
                                      uint32_t *d1) {
  // Compute first share of seed (seed ^ mask).
  uint32_t share0[kEcc256SeedNumWords];
  for (size_t i = 0; i < kEcc256SeedNumWords; i++) {
    share0[i] = seed[i] ^ mask[i];
  }

  // Run the key generation program.
  p256_run_keygen(kEcc256ModePrivateKeyOnly, share0, mask);

  // Read results.
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1));
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
static void p256_ecdsa_gen_keypair(const uint32_t *seed, const uint32_t *mask,
                                   uint32_t *d0, uint32_t *d1, uint32_t *x,
                                   uint32_t *y) {
  // Compute the first share of the seed (seed ^ mask).
  uint32_t share0[kEcc256SeedNumWords];
  for (size_t i = 0; i < kEcc256SeedNumWords; i++) {
    share0[i] = seed[i] ^ mask[i];
  }

  // Run the key generation program.
  p256_run_keygen(kEcc256ModeKeypair, share0, mask);

  // Read results.
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarX, x));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarY, y));
}

/**
 * Simple serial 'k' (secret keygen) command handler.
 *
 * Takes the mask value from the simple serial UART and triggers an OTBN
 * secret key generation operation. The mask must be `kEcc256SeedNumBytes`
 * bytes long.
 *
 * Uses a fixed seed. To overwrite the seed, use the simpleserial command 's'.
 *
 * @param[in] mask The mask provided by the simpleserial UART.
 * @param[in] mask_len Length of the mask.
 */
static void ecc256_ecdsa_secret_keygen(const uint8_t *mask, size_t mask_len) {
  if (mask_len != kEcc256SeedNumBytes) {
    LOG_ERROR("Invalid mask length %hu", (uint8_t)mask_len);
    return;
  }

  // Copy mask to an aligned buffer.
  uint32_t ecc256_mask[kEcc256SeedNumWords];
  memcpy(ecc256_mask, mask, kEcc256SeedNumBytes);

  uint32_t ecc256_d0[kEcc256SeedNumWords];
  uint32_t ecc256_d1[kEcc256SeedNumWords];
  p256_ecdsa_gen_secret_key(ecc256_seed, ecc256_mask, ecc256_d0, ecc256_d1);

  simple_serial_send_packet('r', (unsigned char *)ecc256_d0,
                            kEcc256SeedNumBytes);
  simple_serial_send_packet('r', (unsigned char *)ecc256_d1,
                            kEcc256SeedNumBytes);
}

/**
 * Simple serial 'p' (keypair generation) command handler.
 *
 * Takes the mask value from the simple serial UART and triggers an OTBN
 * secret key generation operation. The mask must be `kEcc256SeedNumBytes`
 * bytes long.
 *
 * Uses a fixed seed. To overwrite the seed, use the simpleserial command 's'.
 *
 * @param[in] mask The mask provided by the simpleserial UART.
 * @param[in] mask_len Length of the mask.
 */
static void ecc256_ecdsa_gen_keypair(const uint8_t *mask, size_t mask_len) {
  if (mask_len != kEcc256SeedNumBytes) {
    LOG_ERROR("Invalid mask length %hu", (uint8_t)mask_len);
    return;
  }

  // Copy mask to an aligned buffer.
  uint32_t ecc256_mask[kEcc256SeedNumWords];
  memcpy(ecc256_mask, mask, kEcc256SeedNumBytes);

  uint32_t ecc256_d0[kEcc256SeedNumWords];
  uint32_t ecc256_d1[kEcc256SeedNumWords];
  uint32_t ecc256_x[kEcc256CoordNumWords];
  uint32_t ecc256_y[kEcc256CoordNumWords];
  p256_ecdsa_gen_keypair(ecc256_seed, ecc256_mask, ecc256_d0, ecc256_d1,
                         ecc256_x, ecc256_y);

  simple_serial_send_packet('r', (unsigned char *)ecc256_d0,
                            kEcc256SeedNumBytes);
  simple_serial_send_packet('r', (unsigned char *)ecc256_d1,
                            kEcc256SeedNumBytes);
  simple_serial_send_packet('r', (unsigned char *)ecc256_x,
                            kEcc256CoordNumBytes);
  simple_serial_send_packet('r', (unsigned char *)ecc256_y,
                            kEcc256CoordNumBytes);
}

/**
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
static void simple_serial_main(void) {
  SS_CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);

  LOG_INFO("Running ECC serial");
  LOG_INFO("Initializing simple serial interface to capture board.");

  simple_serial_init(sca_get_uart());
  SS_CHECK(simple_serial_register_handler(
               'b', ecc256_ecdsa_secret_keygen_batch) == kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('k', ecc256_ecdsa_secret_keygen) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('p', ecc256_ecdsa_gen_keypair) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('x', ecc256_set_seed) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('m', ecc256_en_masks) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('a', ecc256_app_select) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('i', ecc256_modinv_set_input) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('q', ecc256_modinv) ==
           kSimpleSerialOk);

  // load keygen app as default
  LOG_INFO("Load p256 keygen from seed app into OTBN");
  SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256KeyFromSeed));

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}

bool test_main(void) {
  simple_serial_main();
  return true;
}
