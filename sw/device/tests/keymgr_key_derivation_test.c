// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"


OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  CHECK_STATUS_OK(keymgr_testutils_startup(&keymgr, &kmac));

  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  CHECK_STATUS_OK(keymgr_testutils_check_state(
      &keymgr, kDifKeymgrStateOwnerIntermediateKey));
  LOG_INFO("Keymgr entered OwnerIntKey State");

  CHECK_STATUS_OK(keymgr_testutils_generate_identity(&keymgr));
  LOG_INFO("Keymgr generated identity at OwnerIntKey State");

  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, kKeyVersionedParams));
  LOG_INFO("Keymgr generated SW output at OwnerIntKey State");

  // Generate sideload keys for 3 HW interfaces - Kmac, Aes, Otbn.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Kmac at OwnerIntKey State");

  sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Aes at OwnerIntKey State");

  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Otbn at OwnerIntKey State");

  CHECK_STATUS_OK(keymgr_testutils_disable(&keymgr));
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateDisabled));
  LOG_INFO("Keymgr entered Disabled state");

  return true;
}
