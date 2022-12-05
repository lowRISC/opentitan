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
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
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
 * this routine is called.
 *
 * @param otbn_ctx OTBN context object
 * @param[out] result Resulting Montgomery u-coordinate.
 * @param expect_err_bits Error code expected from OTBN ERR register.
 * @return true if the execution is successful (either successful completion
 *         or early exit through an EXPECTED error), otherwise false in case of
 * an unexpected error.
 */
static bool run_x25519_app(otbn_t *otbn_ctx, uint32_t *result,
                           dif_otbn_err_bits_t expect_err_bits) {
  // Copy the input argument (Montgomery u-coordinate).
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, sizeof(kEncodedU), &kEncodedU,
                               kOtbnVarEncU) == kOtbnOk);

  // Run the OTBN program and wait for it to complete.
  LOG_INFO("Starting OTBN program...");
  CHECK(otbn_execute(otbn_ctx) == kOtbnOk);
  if (otbn_busy_wait_for_done(otbn_ctx) != kOtbnOk) {
    // Error during execution; retrieve error bits and instruction count to
    // help with debugging and then exit early.
    dif_otbn_err_bits_t err_bits;
    CHECK(dif_otbn_get_err_bits(&otbn_ctx->dif, &err_bits) == kDifOk);
    uint32_t insn_count;
    CHECK(dif_otbn_get_insn_cnt(&otbn_ctx->dif, &insn_count) == kDifOk);
    LOG_INFO(
        "OTBN encountered an error.\n  Error bits: 0x%08x\n  Instruction "
        "count: 0x%08x",
        err_bits, insn_count);
    CHECK(err_bits == expect_err_bits);
    return true;  // Exit early (return true as CHECK above passes).
  }

  // Check that an error was not expected from OTBN.
  if (expect_err_bits == kOtbnInvalidKeyErr) {
    LOG_ERROR("An error 0x%08x was expected with OTBN and was not encountered.",
              expect_err_bits);
    return false;
  }

  // Copy the result (also a 256-bit Montgomery u-coordinate).
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, 32, kOtbnVarEncResult, result) ==
        kOtbnOk);

  return true;
}

/**
 * Run an OTBN program using a sideloaded key.
 * This routine does not check the correctness of results, merely sideloads the
 * key from keymgr to OTBN and then runs the X25519 program.
 */
static void test_otbn_with_sideloaded_key(dif_keymgr_t *keymgr,
                                          otbn_t *otbn_ctx) {
  // Generate the sideloaded key.
  // TODO(weicai): also check in SV sequence that the key is correct.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  keymgr_testutils_generate_versioned_key(keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for OTBN.");

  // Load the X25519 application.
  CHECK(otbn_load_app(otbn_ctx, kOtbnAppX25519) == kOtbnOk);
  // Run the OTBN app and retrieve the result.
  uint32_t result[8];
  CHECK(run_x25519_app(otbn_ctx, result, kErrBitsOk));

  // Clear the sideload key and check that OTBN errors with the correct error
  // code (`KEY_INVALID` bit 5 = 1).
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleEnabled));
  LOG_INFO("Clearing the Keymgr generated sideload keys.");
  uint32_t at_clear_salt_result[8];
  CHECK(run_x25519_app(otbn_ctx, at_clear_salt_result, kOtbnInvalidKeyErr));

  // Disable sideload key clearing.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleDisabled));
  LOG_INFO("Disable clearing the Keymgr generated sideload keys.");

  // Clear the ERR bits register
  mmio_region_write32(otbn_ctx->dif.base_addr, OTBN_ERR_BITS_REG_OFFSET, 0x0);

  keymgr_testutils_generate_versioned_key(
      keymgr, sideload_params);  // Regenerate the sideload key.
  LOG_INFO("Keymgr generated HW output for OTBN.");
  uint32_t post_clear_salt_result[8];
  // TODO (issue #16653) - fix the function call below
  // and send in kErrBitsOk (error is actually not expected) and uncomment the
  // equality check on outputs afterwards.
  CHECK(run_x25519_app(otbn_ctx, post_clear_salt_result, kOtbnInvalidKeyErr));
  // TODO (issue #16653) - uncomment the equality check on output below.
  // CHECK_ARRAYS_EQ(result, post_clear_salt_result, ARRAYSIZE(result));

  // Change the salt to generate a different key.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  keymgr_testutils_generate_versioned_key(keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for OTBN.");

  uint32_t modified_salt_result[8];
  CHECK(run_x25519_app(otbn_ctx, modified_salt_result, kErrBitsOk));

  // Check that the result with the new key is different from the first
  // result.
  CHECK_ARRAYS_NE(result, modified_salt_result, ARRAYSIZE(result));

  // Change the salt back to generate the first key again.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  keymgr_testutils_generate_versioned_key(keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for OTBN.");

  uint32_t same_key_result[8];
  CHECK(run_x25519_app(otbn_ctx, same_key_result, kErrBitsOk));

  // Check that the result generated using the same key matches the first
  // result.
  CHECK_ARRAYS_EQ(result, same_key_result, ARRAYSIZE(result));
}

bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  keymgr_testutils_startup(&keymgr, &kmac);
  // Advance to OwnerIntermediateKey state.
  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  // Initialize OTBN.
  otbn_t otbn_ctx;
  CHECK(otbn_init(&otbn_ctx, mmio_region_from_addr(
                                 TOP_EARLGREY_OTBN_BASE_ADDR)) == kOtbnOk);
  // Test OTBN sideloading.
  test_otbn_with_sideloaded_key(&keymgr, &otbn_ctx);

  return true;
}
