// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/sca/lib/sca.h"
#include "sw/device/sca/lib/simple_serial.h"
#include "sw/device/sca/otbn_vertical/ecc256_keygen_serial.h"
#include "sw/device/sca/otbn_vertical/ecc256_modinv_serial.h"
#include "sw/ip/entropy_src/test/utils/entropy_testutils.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otbn_regs.h"

/**
 * OpenTitan program for OTBN vertical side-channel analysis.
 *
 * This program implements the following simple serial commands:
 *   - Select the required OTBN app (currently keygen/modinv) ('a')
 *   - Set seed for ecc256 keygen ('x'),
 *   - Secret ecc256 keygen key generation ('k'),
 *   - Ecc256 keygen keypair generation ('p'),
 *   - Ecc256 keygen key generation batch mode ('b')
 *   - Ecc256 keygen enable/disable masks ('m')
 *   - Masked modular inverse computation ('q')
 *   - Get version ('v') (implemented in simpleserial library),
 *   - Seed PRNG ('s') (implemented in simpleserial library),
 * See https://wiki.newae.com/SimpleSerial for details on the protocol.
 */

OTTF_DEFINE_TEST_CONFIG();

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
    // load keygen app
    SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256KeyFromSeed));
  } else if (*app_cmd == 1) {
    // load mod inv app
    SS_CHECK_STATUS_OK(otbn_load_app(kOtbnAppP256ModInv));
  } else {
    LOG_ERROR("Wrong app select command.");
  }
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
  SS_CHECK(simple_serial_register_handler(
               'b', ecc256_ecdsa_keygen_fvsr_seed_batch) == kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler(
               'e', ecc256_ecdsa_keygen_fvsr_key_batch) == kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('k', ecc256_ecdsa_secret_keygen) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('p', ecc256_ecdsa_gen_keypair) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('x', ecc256_set_seed) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('c', ecc256_set_c) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('m', ecc256_en_masks) ==
           kSimpleSerialOk);
  SS_CHECK(simple_serial_register_handler('a', ecc256_app_select) ==
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
