// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * OpenTitan program for OTBN ECDSA-P384 side-channel analysis.
 *
 * This program implements the following simple serial commands:
 *   - Set ephemeral secret key and sign ('p')*,
 *   - Set private key ('d')*,
 *   - Set message ('n')*,
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 * See https://wiki.newae.com/SimpleSerial for details on the protocol.
 *
 * The OTBN-related code was developed based on
 * https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto/ecdsa_p256
 * and
 * https://github.com/lowRISC/opentitan/blob/master/sw/device/tests/crypto/ecdsa_p256_functest.c
 *
 */

OTTF_DEFINE_TEST_CONFIG();

/**
 * Private key d
 * This is the default value used by NewAE in their experiments
 * https://github.com/newaetech/ot-sca/blob/ecc-analysis/reports/ecc/REPORT.md
 * https://github.com/newaetech/opentitan/tree/sca_otbninst
 *
 * The endiannes may need to be fixed.
 *
 * The value of this variable can be overwritten via
 * the simpleserial command `d` (see ecc256_set_private_key_d)
 */
uint8_t ecc256_private_key_d[32] = {
    0xcd, 0xb4, 0x57, 0xaf, 0x1c, 0x9f, 0x4c, 0x74, 0x02, 0x0c, 0x7e,
    0x8b, 0xe9, 0x93, 0x3e, 0x28, 0x0c, 0xf0, 0x18, 0x0d, 0xf4, 0x6c,
    0x0b, 0xda, 0x7a, 0xbb, 0xe6, 0x8f, 0xb7, 0xa0, 0x45, 0x55};

/**
 * Message to sign.
 * The value of this variable can be overwritten via the simpleserial command
 * `n` (see ecc384_set_msg).
 */
uint8_t ecc256_msg[32] = {"Hello OTBN."};

// p256_ecdsa_sca has randomnization removed.
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
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(p256_ecdsa_sca, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(p256_ecdsa_sca, y);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, d0);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, d1);
static const otbn_addr_t kOtbnVarXR = OTBN_ADDR_T_INIT(p256_ecdsa_sca, x_r);
static const otbn_addr_t kOtbnVarK0 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, k0);
static const otbn_addr_t kOtbnVarK1 = OTBN_ADDR_T_INIT(p256_ecdsa_sca, k1);

/**
 * Simple serial 'd' (set private key) command handler.
 *
 * This function does not use key shares to simplify side-channel analysis.
 * The key must be `kAesKeyLength` bytes long.
 *
 * @param key_d Key.
 * @param key_d_len Key length.
 */
static void ecc_256_set_private_key_d(const uint8_t *key_d, size_t key_d_len) {
  SS_CHECK(key_d_len == 32);
  memcpy(ecc256_private_key_d, key_d, key_d_len);
}

/**
 * Simple serial 'n' (set message) command handler.
 *
 * This function does not use key shares to simplify side-channel analysis.
 * The key must be `kAesKeyLength` bytes long.
 *
 * @param msg Message to sign.
 * @param msg_len Message length.
 */
static void ecc_256_set_msg(const uint8_t *msg, size_t msg_len) {
  SS_CHECK(msg_len <= 32);
  memcpy(ecc256_msg, msg, msg_len);
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
static void p256_ecdsa_sign(otbn_t *otbn_ctx, const uint8_t *msg,
                            const uint8_t *private_key_d, uint8_t *signature_r,
                            uint8_t *signature_s, const uint8_t *k) {
  SS_CHECK(otbn_ctx != NULL);

  uint32_t mode = 1;  // mode 1 => sign
  LOG_INFO("Copy data");
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, sizeof(mode), &mode,
                                  kOtbnVarMode) == kOtbnOk);
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, msg,
                                  kOtbnVarMsg) == kOtbnOk);
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, private_key_d,
                                  kOtbnVarD0) == kOtbnOk);
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, k, kOtbnVarK0) ==
           kOtbnOk);

  uint8_t zero[32] = {0};
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, zero,
                                  kOtbnVarD1) == kOtbnOk);
  SS_CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, zero,
                                  kOtbnVarK1) == kOtbnOk);

  LOG_INFO("Execute");
  SS_CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  LOG_INFO("Wait for done");
  SS_CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  LOG_INFO("Get results");
  SS_CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarR,
                                    signature_r) == kOtbnOk);
  SS_CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarS,
                                    signature_s) == kOtbnOk);
  LOG_INFO("r[0]: 0x%02x", signature_r[0]);
  LOG_INFO("s[0]: 0x%02x", signature_s[0]);
}

/**
 * Simple serial 'p' (sign) command handler.
 *
 * Takes the scalar value from the simple serial UART
 * and triggers OTBN_P256_sign operation.
 * Uses a fixed message and private key value
 *
 * To overwrite the message, use the simpleserial command 'n'
 * To overwrite the private key value, use the simpleserial command 'd'
 *
 * @param ecc256_secret_k the ephemeral key/scalar provided via simpleserial
 * UART.
 * @param secret_k_len Length of the ephemeral key.
 */
static void ecc_256_ecdsa(const uint8_t *ecc256_secret_k, size_t secret_k_len) {
  otbn_t otbn_ctx;

  if (secret_k_len != 32) {
    LOG_INFO("Invalid data length %hu", (uint8_t)secret_k_len);
    return;
  }
  LOG_INFO("SSECDSA starting...");
  SS_CHECK(otbn_init(&otbn_ctx, mmio_region_from_addr(
                                    TOP_EARLGREY_OTBN_BASE_ADDR)) == kOtbnOk);
  SS_CHECK(otbn_zero_data_memory(&otbn_ctx) == kOtbnOk);
  SS_CHECK(otbn_load_app(&otbn_ctx, kOtbnAppP256Ecdsa) == kOtbnOk);
  LOG_INFO("otbn_status: 0x%08x",
           mmio_region_read32(
               mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), 0x18));

  uint8_t ecc256_signature_r[32] = {0};
  uint8_t ecc256_signature_s[32] = {0};

  LOG_INFO("Signing");
  sca_set_trigger_high();
  p256_ecdsa_sign(&otbn_ctx, ecc256_msg, ecc256_private_key_d,
                  ecc256_signature_r, ecc256_signature_s, ecc256_secret_k);
  sca_set_trigger_low();

  // TODO: Remove them if they are not necessary for the side-channel analysis.
  simple_serial_send_packet('r', (uint8_t *)ecc256_signature_r, 32);
  simple_serial_send_packet('r', (uint8_t *)ecc256_signature_s, 32);

  LOG_INFO("Clearing OTBN memory");
  SS_CHECK(otbn_zero_data_memory(&otbn_ctx) == kOtbnOk);
}

/**
 * Initializes peripherals and processes simple serial packets received over
 * UART.
 */
static void simple_serial_main(void) {
  entropy_testutils_boot_mode_init();

  sca_init(kScaTriggerSourceOtbn, kScaPeripheralEntropy | kScaPeripheralIoDiv4 |
                                      kScaPeripheralOtbn | kScaPeripheralCsrng |
                                      kScaPeripheralEdn | kScaPeripheralHmac);

  LOG_INFO("Running ECC serial");
  LOG_INFO("Initializing simple serial interface to capture board.");

  simple_serial_init(sca_get_uart());
  SS_CHECK(simple_serial_register_handler('p', ecc_256_ecdsa) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('d', ecc_256_set_private_key_d) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('n', ecc_256_set_msg) ==
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
