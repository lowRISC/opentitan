// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_OTBN_VERTICAL_ECC256_KEYGEN_SERIAL_H_
#define OPENTITAN_SW_DEVICE_SCA_OTBN_VERTICAL_ECC256_KEYGEN_SERIAL_H_

#include "sw/device/lib/crypto/drivers/otbn.h"

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

extern const otbn_app_t kOtbnAppP256KeyFromSeed;

static const otbn_addr_t kOtbnVarMode;
static const otbn_addr_t kOtbnVarSeed0;
static const otbn_addr_t kOtbnVarSeed1;
static const otbn_addr_t kOtbnVarD0;
static const otbn_addr_t kOtbnVarD1;
static const otbn_addr_t kOtbnVarX;
static const otbn_addr_t kOtbnVarY;

/**
 * Simple serial 'm' (set masks enable) command handler.
 *
 * This can be used for batch mode.
 *
 * @param enable 1 => masks enabled, 0 => masks disabled.
 * @param enable_len Length of sent enable value.
 */
void ecc256_en_masks(const uint8_t *enable, size_t enable_len);

/**
 * Simple serial 'x' (set seed) command handler.
 *
 * The seed must be `kEcc256SeedNumBytes` bytes long.
 *
 * @param seed Value for seed share.
 * @param seed_len Length of seed share.
 */
void ecc256_set_seed(const uint8_t *seed, size_t seed_len);

/**
 * Simple serial 'c' (set constant) command handler.
 *
 * The constant must be `kEcc256SeedNumBytes` bytes long.
 *
 * @param C Value of the C constant.
 * @param len Length of the C constant.
 */
void ecc256_set_c(const uint8_t *C, size_t len);

/**
 * Simple serial 'e' (secret keygen fvsr key batch mode) command handler.
 *
 * Collects data for ECDSA keygen fixed-vs-random test in the KEY mode.
 * In the KEY mode, the fixed set of measurements is generated using the fixed
 * 320 bit seed. The random set of measurements is generated in two steps:
 *   1. Choose a random 256 bit number r
 *   2. Compute the seed as (C + r) where C is the fixed 320 bit constant. Note
 * that in this case the used key is equal to (C + r) mod curve_order_n.
 * Takes a number of traces that has to be captured in one batch as input.
 *
 * @param data Value for trace count.
 * @param data_len Length of trace count input.
 */
void ecc256_ecdsa_keygen_fvsr_key_batch(const uint8_t *data, size_t data_len);

/**
 * Simple serial 'b' (secret keygen batch mode) command handler.
 *
 * Collects data for ECDSA keygen fixed-vs-random test in the SEED mode.
 * In the SEED mode, the fixed set of measurements is generated using the fixed
 * 320 bit seed. The random set of measurements is generated using a random 320
 * bit seed. In both cases, the used key is equal to seed mod curve_order_n
 *
 * Takes a number of traces that has to be captured in one batch as input.
 *
 * @param data Value for trace count.
 * @param data_len Length of trace count input.
 */
void ecc256_ecdsa_keygen_fvsr_seed_batch(const uint8_t *data, size_t data_len);

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
void ecc256_ecdsa_secret_keygen(const uint8_t *mask, size_t mask_len);

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
void ecc256_ecdsa_gen_keypair(const uint8_t *mask, size_t mask_len);

#endif  // OPENTITAN_SW_DEVICE_SCA_OTBN_VERTICAL_ECC256_KEYGEN_SERIAL_H_
