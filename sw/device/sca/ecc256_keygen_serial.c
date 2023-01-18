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
};

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
 * Seed value.
 *
 * The default value corresponds to the test data in
 *   sw/otbn/crypto/test/p256_key_from_seed_test.s
 *
 * This default value can be overwritten via the simpleserial command `s`
 * (see ecc256_set_seed)
 */
uint32_t ecc256_seed[kEcc256SeedNumWords] = {
    0x016064e9, 0x11e3f4d6, 0xac3a6fa7, 0xaba11a1b, 0x8f9271d1,
    0x22b79d5f, 0x1176f31d, 0xb5ac3a51, 0x99a082d7, 0x484eb366,
};

/**
 * Simple serial 'x' (set seed) command handler.
 *
 * The key must be `kEcc256SeedNumBytes` bytes long.
 *
 * @param seed Value for seed share.
 * @param seed_len Length of seed share.
 */
static void ecc256_set_seed(const uint8_t *seed, size_t seed_len) {
  SS_CHECK(seed_len == kEcc256SeedNumBytes);
  memcpy(ecc256_seed, seed, seed_len);
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
static void p256_run_keygen(uint32_t mode, const uint32_t *seed,
                            const uint32_t *mask) {
  SS_CHECK(otbn_load_app(kOtbnAppP256KeyFromSeed) == kOtbnErrorOk);

  // Write mode.
  SS_CHECK(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode) ==
           kOtbnErrorOk);

  // Compute first share of seed (seed ^ mask).
  uint32_t seed0[kEcc256SeedNumWords];
  for (size_t i = 0; i < kEcc256SeedNumWords; i++) {
    seed0[i] = seed[i] ^ mask[i];
  }

  // Write seed shares.
  SS_CHECK(otbn_dmem_write(kEcc256SeedNumWords, seed0, kOtbnVarSeed0) ==
           kOtbnErrorOk);
  SS_CHECK(otbn_dmem_write(kEcc256SeedNumWords, mask, kOtbnVarSeed1) ==
           kOtbnErrorOk);

  // Execute program.
  SS_CHECK(otbn_execute() == kOtbnErrorOk);
  SS_CHECK(otbn_busy_wait_for_done() == kOtbnErrorOk);
  /*
  if (otbn_busy_wait_for_done() != kOtbnErrorOk) {
    simple_serial_send_status(otbn_instruction_count_get());
    otbn_err_bits_t err_bits;
    otbn_err_bits_get(&err_bits);
    simple_serial_send_status(err_bits);
  }
  */
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
  // Run the key generation program.
  sca_set_trigger_high();
  p256_run_keygen(kEcc256ModePrivateKeyOnly, seed, mask);
  sca_set_trigger_low();

  // Read results.
  SS_CHECK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0) == kOtbnErrorOk);
  SS_CHECK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1) == kOtbnErrorOk);
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
  // Run the key generation program.
  sca_set_trigger_high();
  p256_run_keygen(kEcc256ModeKeypair, seed, mask);
  sca_set_trigger_low();

  // Read results.
  SS_CHECK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD0, d0) == kOtbnErrorOk);
  SS_CHECK(otbn_dmem_read(kEcc256SeedNumWords, kOtbnVarD1, d1) == kOtbnErrorOk);
  SS_CHECK(otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarX, x) == kOtbnErrorOk);
  SS_CHECK(otbn_dmem_read(kEcc256CoordNumWords, kOtbnVarY, y) == kOtbnErrorOk);
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

  LOG_INFO("Running keygen...");
  uint32_t ecc256_d0[kEcc256SeedNumWords];
  uint32_t ecc256_d1[kEcc256SeedNumWords];
  p256_ecdsa_gen_secret_key(ecc256_seed, ecc256_mask, ecc256_d0, ecc256_d1);

  simple_serial_send_packet('r', (unsigned char *) &kOtbnVarD0, sizeof(otbn_addr_t));
  simple_serial_send_packet('r', (unsigned char *) &kOtbnVarD1, sizeof(otbn_addr_t));
  simple_serial_send_packet('r', (unsigned char *) ecc256_d0, kEcc256SeedNumBytes);
  simple_serial_send_packet('r', (unsigned char *) ecc256_d1, kEcc256SeedNumBytes);

  LOG_INFO("Clearing OTBN memory.");
  SS_CHECK(otbn_dmem_sec_wipe() == kOtbnErrorOk);
  SS_CHECK(otbn_imem_sec_wipe() == kOtbnErrorOk);
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

  LOG_INFO("Running keygen...");
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

  LOG_INFO("Clearing OTBN memory.");
  SS_CHECK(otbn_dmem_sec_wipe() == kOtbnErrorOk);
  SS_CHECK(otbn_imem_sec_wipe() == kOtbnErrorOk);
}

/**
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
static void simple_serial_main(void) {
  entropy_testutils_auto_mode_init();

  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);

  LOG_INFO("Running ECC serial");
  LOG_INFO("Initializing simple serial interface to capture board.");

  simple_serial_init(sca_get_uart());
  SS_CHECK(simple_serial_register_handler('k', ecc256_ecdsa_secret_keygen) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('p', ecc256_ecdsa_gen_keypair) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('x', ecc256_set_seed) ==
           kSimpleSerialOk);

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}

bool test_main(void) {
  simple_serial_main();
  return true;
}
