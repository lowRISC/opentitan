// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"
#include "sw/ip/entropy_src/test/utils/entropy_testutils.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otbn_regs.h"

/**
 * OpenTitan program for OTBN ECDSA-P384 side-channel analysis.
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
 */

OTTF_DEFINE_TEST_CONFIG();

enum {
  /**
   * Number of bytes for ECDSA P-384 private keys, message digests, and point
   * coordinates.
   */
  kEcc384NumBytes = 384 / 8,
  /**
   * Number of 32b words for ECDSA P-384 private keys, message digests, and
   * point coordinates.
   *
   * Note: Since this is not an even multiple of `kOtbnWideWordNumWords`, the
   * caller needs to write zeroes to OTBN to fill out the last wide word.
   * Otherwise, OTBN will encounter an error when it tries to read the
   * uninitialized data.
   */
  kEcc384NumWords = kEcc384NumBytes / sizeof(uint32_t),
};

/**
 * Two shares of the ephemeral secret key k
 * k = k0 + k1
 * k0 = ecc384_secret_k[0:11] (0x00000000...ffffffff)
 * k1 = ecc384_secret_k[12:23] (0x00000000...00000000)
 *
 * The default values can be overwritten via
 * the simpleserial command `k` (see ecc384_set_private_key_d)
 */
uint32_t ecc384_secret_k[2 * kEcc384NumWords] = {
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

/**
 * Private key d
 * I took this from here: https://www.rfc-editor.org/rfc/rfc6979#page-33
 * The endianness may need to be fixed.
 *
 * Delivered as 2 shares. The second share is set to all-zero by default.
 *
 * The value of this variable can be overwritten via the simpleserial command
 * `d` (see ecc384_set_private_key_d)
 */
uint32_t ecc384_private_key_d[2 * kEcc384NumWords] = {
    0xAD3D9D6B, 0x1C8C1B2E, 0x7598B105, 0x4D9F65B6, 0x663B3CE2, 0xBA97F27B,
    0x4077A49A, 0xD8377178, 0x4E72D596, 0x25A8704C, 0xEAC972F8, 0xF5EDD260,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
};

/**
 * Message to sign
 * The value of this variable can be overwritten via the simpleserial command
 * `n` (see ecc384_set_msg).
 */
uint32_t ecc384_msg[kEcc384NumWords] = {
    0x48656c6c,  // 'Hell'
    0x6f204f54,  // 'o OT'
    0x424e0000,  // 'BN'
};

// p384_ecdsa_sca has randomnization removed.
OTBN_DECLARE_APP_SYMBOLS(p384_ecdsa_sca);

OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, mode);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, msg);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, r);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, s);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, x);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, y);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, d0);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, d1);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, k0);
OTBN_DECLARE_SYMBOL_ADDR(p384_ecdsa_sca, k1);

static const otbn_app_t kOtbnAppP384Ecdsa = OTBN_APP_T_INIT(p384_ecdsa_sca);

static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(p384_ecdsa_sca, mode);
static const otbn_addr_t kOtbnVarMsg = OTBN_ADDR_T_INIT(p384_ecdsa_sca, msg);
static const otbn_addr_t kOtbnVarR = OTBN_ADDR_T_INIT(p384_ecdsa_sca, r);
static const otbn_addr_t kOtbnVarS = OTBN_ADDR_T_INIT(p384_ecdsa_sca, s);
static const otbn_addr_t kOtbnVarX = OTBN_ADDR_T_INIT(p384_ecdsa_sca, x);
static const otbn_addr_t kOtbnVarY = OTBN_ADDR_T_INIT(p384_ecdsa_sca, y);
static const otbn_addr_t kOtbnVarD0 = OTBN_ADDR_T_INIT(p384_ecdsa_sca, d0);
static const otbn_addr_t kOtbnVarD1 = OTBN_ADDR_T_INIT(p384_ecdsa_sca, d1);
static const otbn_addr_t kOtbnVarK0 = OTBN_ADDR_T_INIT(p384_ecdsa_sca, k0);
static const otbn_addr_t kOtbnVarK1 = OTBN_ADDR_T_INIT(p384_ecdsa_sca, k1);

/**
 * Simple serial 'k' (set ephemeral key) command handler.
 *
 * This function sets both shares of the secret scalar k.
 * The first 48 bytes (i.e, kEcc384NumBytes) are used as k0, and
 * The last 48 bytes (i.e, kEcc384NumBytes) are used as k1.
 *
 * Any of the shares can be set to all zeros to simplify the SCA.
 *
 * As this function sets both shares,
 * the data length must be `2*kEcc384NumBytes`.
 *
 * @param secret_k Key.
 * @param secret_k_len Key length.
 */
static void ecc384_set_secret_key_k(const uint8_t *secret_k,
                                    size_t secret_k_len) {
  SS_CHECK(secret_k_len == 2 * kEcc384NumBytes);
  memcpy(ecc384_secret_k, secret_k, secret_k_len);
}

/**
 * Simple serial 'd' (set private key) command handler.
 *
 * This function sets both shares of the private key d.
 * The first 48 bytes (i.e, kEcc384NumBytes) are used as d0, and
 * The last 48 bytes (i.e, kEcc384NumBytes) are used as d1.
 *
 * Any of the shares can be set to all zeros to simplify the SCA.
 *
 * As this function sets both shares,
 * the data length must be `2*kEcc384NumBytes`.
 *
 * @param key_d Key.
 * @param key_d_len Key length.
 */
static void ecc_384_set_private_key_d(const uint8_t *key_d, size_t key_d_len) {
  SS_CHECK(key_d_len == 2 * kEcc384NumBytes);
  memcpy(ecc384_private_key_d, key_d, key_d_len);
}

/**
 * Simple serial 'n' (set message) command handler.
 *
 * This implementation skips hashing the message to simplify side-channel
 * analysis, so the message must not be longer than `kEcc384NumBytes` bytes
 * long.
 *
 * @param msg Message to sign.
 * @param msg_len Message length.
 */
static void ecc384_set_msg(const uint8_t *msg, size_t msg_len) {
  SS_CHECK(msg_len <= kEcc384NumBytes);
  // Reset to zero before copying (in case of a short message).
  memset(ecc384_msg, 0, kEcc384NumBytes);
  memcpy(ecc384_msg, msg, msg_len);
}

/**
 * Write a 384-bit value to OTBN.
 *
 * This function actually writes 512 bits -- 384 bits with the real data and
 * the rest with zeroes -- to avoid read-of-uninitialized-data errors during
 * OTBN execution.
 */
static void p384_dmem_write(const uint32_t src[kEcc384NumWords],
                            const otbn_addr_t dest) {
  static const uint32_t zero[kEcc384NumWords % kOtbnWideWordNumWords] = {0};
  SS_CHECK_STATUS_OK(otbn_dmem_write(kEcc384NumWords, src, dest));
  SS_CHECK_STATUS_OK(otbn_dmem_write(ARRAYSIZE(zero), zero, dest));
}

/**
 * Signs a message with ECDSA using the P-384 curve.
 *
 * R = k*G
 * r = x-coordinate of R
 * s = k^(-1)(msg + r*d)  mod n
 *
 * @param otbn_ctx            The OTBN context object.
 * @param msg                 The message to sign, msg (48B).
 * @param private_key_d       The private key d (48B).
 * @param k                   The ephemeral key k (random scalar) (48B).
 * @param[out] signature_r    Signature component r (the x-coordinate of R).
 *                            Provide a pre-allocated 48B buffer.
 * @param[out] signature_s    Signature component s (the proof).
 *                            Provide a pre-allocated 48B buffer.
 */
static void p384_ecdsa_sign(const uint32_t *msg, const uint32_t *private_key_d,
                            uint32_t *signature_r, uint32_t *signature_s,
                            const uint32_t *k) {
  uint32_t mode = 1;  // mode 1 => sign
  // LOG_INFO("Copy data");
  SS_CHECK_STATUS_OK(otbn_dmem_write(/*num_words=*/1, &mode, kOtbnVarMode));
  p384_dmem_write(msg, kOtbnVarMsg);
  p384_dmem_write(private_key_d, kOtbnVarD0);
  p384_dmem_write(private_key_d + kEcc384NumWords, kOtbnVarD1);

  SS_CHECK_STATUS_OK(otbn_dmem_write(kEcc384NumWords, k, kOtbnVarK0));
  SS_CHECK_STATUS_OK(
      otbn_dmem_write(kEcc384NumWords, k + kEcc384NumWords, kOtbnVarK1));

  SS_CHECK_STATUS_OK(otbn_execute());
  SS_CHECK_STATUS_OK(otbn_busy_wait_for_done());

  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc384NumWords, kOtbnVarR, signature_r));
  SS_CHECK_STATUS_OK(otbn_dmem_read(kEcc384NumWords, kOtbnVarS, signature_s));
}

/**
 * Simple serial 'p' (sign) command handler.
 *
 * Takes the scalar value from the simple serial UART and triggers
 * OTBN_P384_sign operation.
 *
 * To overwrite the message, use the simpleserial command 'n'
 * To overwrite the private key value, use the simpleserial command 'd'
 *
 * @param ecc384_secret_k the ephemeral key/scalar provided via simpleserial
 * UART.
 * @param secret_k_len Length of the ephemeral key.
 */
static void ecc384_ecdsa(const uint8_t *ecc384_secret_k_bytes,
                         size_t secret_k_len) {
  LOG_INFO("SSECDSA starting...");
  SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP384Ecdsa));
  LOG_INFO(
      "otbn_status: 0x%08x",
      abs_mmio_read32(TOP_DARJEELING_OTBN_BASE_ADDR + OTBN_STATUS_REG_OFFSET));

  uint32_t ecc384_signature_r[kEcc384NumWords];
  uint32_t ecc384_signature_s[kEcc384NumWords];

  LOG_INFO("Signing");
  sca_set_trigger_high();
  p384_ecdsa_sign(ecc384_msg, ecc384_private_key_d, ecc384_signature_r,
                  ecc384_signature_s, ecc384_secret_k);
  sca_set_trigger_low();

  // Copy r and s into byte buffers to avoid strict-aliasing violations.
  uint8_t ecc384_signature_r_bytes[kEcc384NumBytes];
  memcpy(ecc384_signature_r_bytes, ecc384_signature_r,
         sizeof(ecc384_signature_r));
  uint8_t ecc384_signature_s_bytes[kEcc384NumBytes];
  memcpy(ecc384_signature_s_bytes, ecc384_signature_s,
         sizeof(ecc384_signature_s));

  /**
   * Send the signature_r and signature_s back to host
   *
   * TODO: Remove them if they are not necessary for the side-channel analysis.
   */
  simple_serial_send_packet('r', ecc384_signature_r_bytes, kEcc384NumBytes);
  simple_serial_send_packet('r', ecc384_signature_s_bytes, kEcc384NumBytes);

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

  sca_init(kScaTriggerSourceOtbn, kScaPeripheralIoDiv4 | kScaPeripheralOtbn |
                                      kScaPeripheralCsrng | kScaPeripheralEdn |
                                      kScaPeripheralHmac);

  LOG_INFO("Running ECC serial");
  LOG_INFO("Initializing simple serial interface to capture board.");
  simple_serial_init(sca_get_uart());

  SS_CHECK(simple_serial_register_handler('p', ecc384_ecdsa) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('k', ecc384_set_secret_key_k) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('d', ecc_384_set_private_key_d) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('n', ecc384_set_msg) ==
           kSimpleSerialOk);

  LOG_INFO("Starting simple serial packet handling.");
  while (true) {
    simple_serial_process_packet();
  }
}

bool test_main(void) {
  (void)kOtbnVarX;
  (void)kOtbnVarY;

  simple_serial_main();
  return true;
}
