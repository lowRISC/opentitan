// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otbn_regs.h"  // Generated.

/* Set up pointers to symbols in the OTBN application. */
OTBN_DECLARE_APP_SYMBOLS(x25519_sideload);
OTBN_DECLARE_SYMBOL_ADDR(x25519_sideload, enc_u);
OTBN_DECLARE_SYMBOL_ADDR(x25519_sideload, enc_result);
static const otbn_app_t kOtbnAppX25519 = OTBN_APP_T_INIT(x25519_sideload);
static const otbn_addr_t kOtbnVarEncU =
    OTBN_ADDR_T_INIT(x25519_sideload, enc_u);
static const otbn_addr_t kOtbnVarEncResult =
    OTBN_ADDR_T_INIT(x25519_sideload, enc_result);

OTTF_DEFINE_TEST_CONFIG();

/**
 * Encoded Montgomery u-coordinate for testing.
 *
 * This value (9) is actually the u-coordinate of the Curve25519 base point, so
 * the X25519 function will effectively compute the public key. This is the
 * first step in key exchange (see RFC 7748, section 6.1).
 */
static const uint32_t kEncodedU[8] = {
    0x9, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};
static const dif_otbn_err_bits_t kOtbnInvalidKeyErr =
    0x1 << OTBN_ERR_BITS_KEY_INVALID_BIT;
static const dif_otbn_err_bits_t kErrBitsOk = 0x0;

/**
 * Runs the OTBN X25519 application.
 *
 * The X25519 app and sideloaded key should already be loaded into OTBN before
 * this routine is called. Causes CHECK-fail if the OTBN error code is not as
 * expected.
 *
 * @param otbn OTBN context object
 * @param[out] result Resulting Montgomery u-coordinate.
 * @param expect_err_bits Error code expected from OTBN ERR register.
 * an unexpected error.
 */
static void run_x25519_app(dif_otbn_t *otbn, uint32_t *result,
                           dif_otbn_err_bits_t expect_err_bits) {
  // Copy the input argument (Montgomery u-coordinate).
  CHECK_STATUS_OK(otbn_testutils_write_data(otbn, sizeof(kEncodedU), &kEncodedU,
                                            kOtbnVarEncU));

  // Run the OTBN program and wait for it to complete.
  LOG_INFO("Starting OTBN program...");
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, expect_err_bits));

  // Copy the result (also a 256-bit Montgomery u-coordinate).
  CHECK_STATUS_OK(
      otbn_testutils_read_data(otbn, 32, kOtbnVarEncResult, result));
}

/**
 * Run an OTBN program using a sideloaded key.
 * This routine does not check the correctness of results, merely sideloads the
 * key from keymgr to OTBN and then runs the X25519 program.
 */
static void test_otbn_with_sideloaded_key(dif_keymgr_t *keymgr,
                                          dif_otbn_t *otbn) {
  // Generate the sideloaded key.
  // TODO(weicai): also check in SV sequence that the key is correct.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for OTBN.");

  // Load the X25519 application.
  CHECK_STATUS_OK(otbn_testutils_load_app(otbn, kOtbnAppX25519));
  // Run the OTBN app and retrieve the result.
  uint32_t result[8];
  run_x25519_app(otbn, result, kErrBitsOk);

#ifdef TEST_SIMPLE_CASE_ONLY
  return;
#endif

  // Clear the sideload key and check that OTBN errors with the correct error
  // code (`KEY_INVALID` bit 5 = 1).
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleEnabled));
  LOG_INFO("Clearing the Keymgr generated sideload keys.");
  uint32_t at_clear_salt_result[8];
  run_x25519_app(otbn, at_clear_salt_result, kOtbnInvalidKeyErr);

  // Disable sideload key clearing.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleDisabled));
  LOG_INFO("Disable clearing the Keymgr generated sideload keys.");

  // Clear the ERR bits register
  mmio_region_write32(otbn->base_addr, OTBN_ERR_BITS_REG_OFFSET, 0x0);

  CHECK_STATUS_OK(keymgr_testutils_generate_versioned_key(
      keymgr, sideload_params));  // Regenerate the sideload key.
  LOG_INFO("Keymgr generated HW output for OTBN.");
  uint32_t post_clear_salt_result[8];
  run_x25519_app(otbn, post_clear_salt_result, kErrBitsOk);
  CHECK_ARRAYS_EQ(result, post_clear_salt_result, ARRAYSIZE(result));

  // Change the salt to generate a different key.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for OTBN.");

  uint32_t modified_salt_result[8];
  run_x25519_app(otbn, modified_salt_result, kErrBitsOk);

  // Check that the result with the new key is different from the first
  // result.
  CHECK_ARRAYS_NE(result, modified_salt_result, ARRAYSIZE(result));

  // Change the salt back to generate the first key again.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for OTBN.");

  uint32_t same_key_result[8];
  run_x25519_app(otbn, same_key_result, kErrBitsOk);

  // Check that the result generated using the same key matches the first
  // result.
  CHECK_ARRAYS_EQ(result, same_key_result, ARRAYSIZE(result));
}

bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  CHECK_STATUS_OK(keymgr_testutils_startup(&keymgr, &kmac));
  // Advance to OwnerIntermediateKey state.
  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  CHECK_STATUS_OK(keymgr_testutils_check_state(
      &keymgr, kDifKeymgrStateOwnerIntermediateKey));
  LOG_INFO("Keymgr entered OwnerIntKey State");

  // Initialize OTBN.
  dif_otbn_t otbn;
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Put entropy source into auto mode. If the entropy source was merely left
  // with the entropy it generated at boot, this test may exhaust the supply
  // with no renewal.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // Test OTBN sideloading.
  test_otbn_with_sideloaded_key(&keymgr, &otbn);

  return true;
}
