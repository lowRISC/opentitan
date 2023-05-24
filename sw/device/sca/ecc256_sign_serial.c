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
 *   - Set ephemeral secret key ('k')*,
 *   - Set private key ('d')*,
 *   - Set message ('n')*,
 *   - Start signing ('p')*
 *   - Version ('v')+,
 *   - Seed PRNG ('s')+,
 * Commands marked with * are implemented in this file. Those marked with + are
 * implemented in the simple serial library.
 * See https://wiki.newae.com/SimpleSerial for details on the protocol.
 *
 * The OTBN-related code was developed based on
 * https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto/ecc/ecdsa_p256.c
 * and
 * https://github.com/lowRISC/opentitan/blob/master/sw/device/tests/crypto/ecdsa_p256_functest.c
 *
 */

OTTF_DEFINE_TEST_CONFIG();

enum {
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
};

/**
 * Two shares of the ephemeral secret key k
 * k = k0 + k1
 * k0 = ecc256_secret_k[0:7] (0x00000000...ffffffff)
 * k1 = ecc256_secret_k[8:15] (0x00000000...00000000)
 *
 * The default values can be overwritten via
 * the simpleserial command `k` (see ecc256_set_private_key_d)
 */
uint32_t ecc256_secret_k[2 * kEcc256NumWords] = {
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

/**
 * Private key d
 * This is the default value used by NewAE in their experiments
 * https://github.com/newaetech/ot-sca/blob/ecc-analysis/reports/ecc/REPORT.md
 * https://github.com/newaetech/opentitan/tree/sca_otbninst
 *
 *
 * The value of this variable can be overwritten via
 * the simpleserial command `d` (see ecc256_set_private_key_d)
 */
uint32_t ecc256_private_key_d[2 * kEcc256NumWords] = {
    0xaf57b4cd, 0x744c9f1c, 0x8b7e0c02, 0x283e93e9, 0x0d18f00c, 0xda0b6cf4,
    0x8fe6bb7a, 0x5545a0b7, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

/**
 * Message to sign.
 *
 * The value of this variable can be overwritten via the simpleserial command
 * `n` (see ecc256_set_msg).
 */
uint32_t ecc256_msg[kEcc256NumWords] = {
    0x48656c6c,  // 'Hell'
    0x6f204f54,  // 'o OT'
    0x424e0000,  // 'BN'
};

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
 * Simple serial 'k' (set ephemeral key) command handler.
 *
 * This function sets both shares of the secret scalar k.
 * The first 32 bytes (i.e, kEcc256NumBytes) are used as k0, and
 * The last 32 bytes (i.e, kEcc256NumBytes) are used as k1.
 *
 * Any of the shares can be set to all zeros to simplify the SCA.
 *
 * As this function sets both shares,
 * the data length must be `2*kEcc256NumBytes`.
 *
 * @param secret_k Key.
 * @param secret_k_len Key length.
 */
static void ecc256_set_secret_key_k(const uint8_t *secret_k,
                                    size_t secret_k_len) {
  SS_CHECK(secret_k_len == 2 * kEcc256NumBytes);
  memcpy(ecc256_secret_k, secret_k, secret_k_len);
}

/**
 * Simple serial 'd' (set private key) command handler.
 *
 * This function sets both shares of the private key d.
 * The first 32 bytes (i.e, kEcc256NumBytes) are used as d0, and
 * The last 32 bytes (i.e, kEcc256NumBytes) are used as d1.
 *
 * Any of the shares can be set to all zeros to simplify the SCA.
 *
 * As this function sets both shares,
 * the data length must be `2*kEcc256NumBytes`.
 *
 * @param key_d Key.
 * @param key_d_len Key length.
 */
static void ecc256_set_private_key_d(const uint8_t *key_d, size_t key_d_len) {
  SS_CHECK(key_d_len == 2 * kEcc256NumBytes);
  memcpy(ecc256_private_key_d, key_d, key_d_len);
}

/**
 * Simple serial 'n' (set message) command handler.
 *
 * This implementation skips hashing the message to simplify side-channel
 * analysis, so the message must not be longer than `kEcc256NumBytes` bytes
 * long.
 *
 * @param msg Message to sign.
 * @param msg_len Message length.
 */
static void ecc256_set_msg(const uint8_t *msg, size_t msg_len) {
  SS_CHECK(msg_len <= kEcc256NumBytes);
  // Reset to zero before copying.
  memset(ecc256_msg, 0, kEcc256NumBytes);
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
static void p256_ecdsa_sign(const uint32_t *msg, const uint32_t *private_key_d,
                            uint32_t *signature_r, uint32_t *signature_s,
                            const uint32_t *k) {
  uint32_t mode = 1;  // mode 1 => sign
  // Send operation mode to OTBN
  SS_CHECK_STATUS_OK(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode));
  // Send Msg to OTBN
  SS_CHECK_STATUS_OK(otbn_dmem_write(kEcc256NumWords, msg, kOtbnVarMsg));
  // Send two shares of private_key_d to OTBN
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256NumWords, private_key_d, kOtbnVarD0));
  SS_CHECK_STATUS_OK(otbn_dmem_write(
      kEcc256NumWords, private_key_d + kEcc256NumWords, kOtbnVarD1));
  // Send two shares of secret_k to OTBN
  SS_CHECK_STATUS_OK(otbn_dmem_write(kEcc256NumWords, k, kOtbnVarK0));
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc256NumWords, k + kEcc256NumWords, kOtbnVarK1));

  // Start OTBN execution
  SS_CHECK_STATUS_OK(otbn_execute());
  SS_CHECK_STATUS_OK(otbn_busy_wait_for_done());

  // Read the results back (sig_r, sig_s)
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256NumWords, kOtbnVarR, signature_r));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc256NumWords, kOtbnVarS, signature_s));
}

/**
 * Simple serial 'p' (sign) command handler.
 *
 * Triggers OTBN_P256_sign operation.
 *
 */
static void ecc256_ecdsa(const uint8_t *arg, size_t len) {
  LOG_INFO("SSECDSA starting...");
  SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256Ecdsa));
  LOG_INFO("otbn_status: 0x%08x", abs_mmio_read32(TOP_EARLGREY_OTBN_BASE_ADDR +
                                                  OTBN_STATUS_REG_OFFSET));

  uint32_t ecc256_signature_r[kEcc256NumWords];
  uint32_t ecc256_signature_s[kEcc256NumWords];

  LOG_INFO("Signing");
  sca_set_trigger_high();
  p256_ecdsa_sign(ecc256_msg, ecc256_private_key_d, ecc256_signature_r,
                  ecc256_signature_s, ecc256_secret_k);
  sca_set_trigger_low();

  // Copy r and s into byte buffers to avoid strict-aliasing violations.
  uint8_t ecc256_signature_r_bytes[kEcc256NumBytes];
  memcpy(ecc256_signature_r_bytes, ecc256_signature_r,
         sizeof(ecc256_signature_r));
  uint8_t ecc256_signature_s_bytes[kEcc256NumBytes];
  memcpy(ecc256_signature_s_bytes, ecc256_signature_s,
         sizeof(ecc256_signature_s));

  // Send the outputs to the Host (Python) through simpleserial protocol.
  simple_serial_send_packet('r', ecc256_signature_r_bytes, kEcc256NumBytes);
  simple_serial_send_packet('r', ecc256_signature_s_bytes, kEcc256NumBytes);

  // Clear OTBN memory
  SS_CHECK_STATUS_OK(otbn_dmem_sec_wipe());
  SS_CHECK_STATUS_OK(otbn_imem_sec_wipe());
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
  SS_CHECK(simple_serial_register_handler('p', ecc256_ecdsa) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('k', ecc256_set_secret_key_k) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('d', ecc256_set_private_key_d) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('n', ecc256_set_msg) ==
           kSimpleSerialOk);

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}

bool test_main(void) {
  (void)kOtbnVarX;
  (void)kOtbnVarY;
  (void)kOtbnVarXR;

  simple_serial_main();
  return true;
}
