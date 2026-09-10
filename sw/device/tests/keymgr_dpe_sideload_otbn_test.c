// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/otbn_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;
static dif_otbn_t otbn;

static const dt_otbn_t kOtbnDt = (dt_otbn_t)0;

/* Set up pointers to symbols in the OTBN application. */
OTBN_DECLARE_APP_SYMBOLS(run_curve25519);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, mode);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, MODE_X25519_KEYGEN_SIDELOAD);
OTBN_DECLARE_SYMBOL_ADDR(run_curve25519, x25519_public_key);
static const otbn_app_t kOtbnAppX25519 = OTBN_APP_T_INIT(run_curve25519);
static const otbn_addr_t kOtbnVarMode = OTBN_ADDR_T_INIT(run_curve25519, mode);
static const uint32_t kOtbnCurve25519ModeX25519KeygenSideload =
    OTBN_ADDR_T_INIT(run_curve25519, MODE_X25519_KEYGEN_SIDELOAD);
static const otbn_addr_t kOtbnVarX25519PublicKey =
    OTBN_ADDR_T_INIT(run_curve25519, x25519_public_key);

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles(void) {
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_keymgr_dpe_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR), &keymgr_dpe));
  CHECK_DIF_OK(dif_otbn_init_from_dt(kOtbnDt, &otbn));
}

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
  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(otbn, /*enable=*/false));

  uint32_t mode = kOtbnCurve25519ModeX25519KeygenSideload;
  CHECK_STATUS_OK(
      otbn_testutils_write_data(otbn, sizeof(mode), &mode, kOtbnVarMode));

  // Run the OTBN program and wait for it to complete. Clear software
  // error fatal flag as the test expects an intermediate error state.
  LOG_INFO("Starting OTBN program...");
  CHECK_DIF_OK(dif_otbn_set_ctrl_software_errs_fatal(otbn, false));
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, expect_err_bits));

  CHECK_STATUS_OK(
      otbn_testutils_read_data(otbn, 32, kOtbnVarX25519PublicKey, result));
}

/**
 * Run an OTBN program using a sideloaded key.
 * This routine does not check the correctness of results, merely sideloads the
 * key from keymgr to OTBN and then runs the X25519 program.
 */
static void test_otbn_with_sideloaded_key(dif_keymgr_dpe_t *keymgr_dpe,
                                          dif_otbn_t *otbn) {
  // Generate the sideloaded key.
  // TODO(weicai): also check in SV sequence that the key is correct.
  dif_keymgr_dpe_generate_params_t sideload_params = kKeyVersionedParams;
  sideload_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  sideload_params.sideload_key = true;
  // Ensure the slot matches with the CreatorRootKey
  sideload_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;

  // Check the applied key version
  uint32_t max_key_version = kCreatorRootKeyParams.max_key_version;
  if (sideload_params.version > max_key_version) {
    LOG_INFO("Key version %d is greater than the maximum key version %d",
             sideload_params.version, max_key_version);
    LOG_INFO("Setting key version to the maximum key version %d",
             max_key_version);
    sideload_params.version = max_key_version;
  }

  // Generate the OTBN key
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(keymgr_dpe, &sideload_params));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated HW output for OTBN from the CreatorRootKey");

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
  CHECK_STATUS_OK(ottf_alerts_expect_alert_start(
      dt_otbn_alert_to_alert_id(kOtbnDt, kDtOtbnAlertRecov)));
  CHECK_STATUS_OK(keymgr_dpe_testutils_clear_sideload_key(
      keymgr_dpe, kDifKeymgrDpeSideLoadClearOtbn));
  LOG_INFO("Clearing the KeymgrDpe generated sideload keys.");
  uint32_t at_clear_salt_result[8];
  run_x25519_app(otbn, at_clear_salt_result, kOtbnInvalidKeyErr);
  CHECK_STATUS_OK(ottf_alerts_expect_alert_finish(
      dt_otbn_alert_to_alert_id(kOtbnDt, kDtOtbnAlertRecov)));
  // Stop clearing the sideload OTBN key
  CHECK_STATUS_OK(keymgr_dpe_testutils_clear_sideload_key(
      keymgr_dpe, kDifKeymgrDpeSideLoadClearNone));

  // Clear the ERR bits register
  mmio_region_write32(otbn->base_addr, OTBN_ERR_BITS_REG_OFFSET, 0x0);

  // Regenerate the original OTBN key and verify against the privious result
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(keymgr_dpe, &sideload_params));
  LOG_INFO("KeymgrDpe regenerated HW output for OTBN.");
  uint32_t post_clear_salt_result[8];
  run_x25519_app(otbn, post_clear_salt_result, kErrBitsOk);
  CHECK_ARRAYS_EQ(result, post_clear_salt_result, ARRAYSIZE(result));

  // Change the salt to generate a different key.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(keymgr_dpe, &sideload_params));
  LOG_INFO("KeymgrDpe generated different HW output for OTBN.");

  uint32_t modified_salt_result[8];
  run_x25519_app(otbn, modified_salt_result, kErrBitsOk);

  // Check that the result with the new key is different from the first
  // result.
  CHECK_ARRAYS_NE(result, modified_salt_result, ARRAYSIZE(result));

  // Change the salt back to generate the first key again.
  sideload_params.salt[0] = ~sideload_params.salt[0];
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(keymgr_dpe, &sideload_params));
  LOG_INFO("KeymgrDpe generated the original HW output for OTBN.");

  uint32_t same_key_result[8];
  run_x25519_app(otbn, same_key_result, kErrBitsOk);

  // Check that the result generated using the same key matches the first
  // result.
  CHECK_ARRAYS_EQ(result, same_key_result, ARRAYSIZE(result));
}

bool test_main(void) {
  // Start keymgr_dpe, generating CreatorRootKey into the slot defined by
  // kCreatorRootKeyParams(/sw/device/lib/testing/keymgr_dpe_testutils.h)
  CHECK_STATUS_OK(keymgr_dpe_testutils_startup(&keymgr_dpe, &kmac));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  // Init the otbn
  CHECK_DIF_OK(dif_otbn_init_from_dt(kOtbnDt, &otbn));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived CreatorRootKey and removed the UDS");
  LOG_INFO("KeymgrDpe is ready for the OTBN test!");

  // Test OTBN sideloading.
  test_otbn_with_sideloaded_key(&keymgr_dpe, &otbn);

  return true;
}
