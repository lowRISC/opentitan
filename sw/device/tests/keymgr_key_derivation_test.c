// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;

  // Initialize keymgr and advance to the state specified by the loaded ROM.
  CHECK_STATUS_OK(keymgr_testutils_initialize(&keymgr, &kmac));

  const char *state_name;
  CHECK_STATUS_OK(keymgr_testutils_state_string_get(&keymgr, &state_name));

  LOG_INFO("Keymgr entered %s State", state_name);

  CHECK_STATUS_OK(keymgr_testutils_generate_identity(
      &keymgr,
      (dif_keymgr_identity_seed_params_t){.cdi_type = kDifKeymgrSealingCdi}));
  LOG_INFO("Keymgr generated identity at %s State", state_name);

  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;

  // Get the maximum key version supported by the keymgr in its current state.
  uint32_t max_key_version;
  CHECK_STATUS_OK(
      keymgr_testutils_max_key_version_get(&keymgr, &max_key_version));

  if (sideload_params.version > max_key_version) {
    LOG_INFO("Key version %d is greater than the maximum key version %d",
             sideload_params.version, max_key_version);
    LOG_INFO("Setting key version to the maximum key version %d",
             max_key_version);
    sideload_params.version = max_key_version;
  }

  // Generate sw versioned key.
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated SW output at %s State", state_name);

  // Generate sideload keys for 3 HW interfaces - Kmac, Aes, Otbn.
  sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Kmac at %s State", state_name);

  sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Aes at %sState", state_name);

  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Otbn at %s State", state_name);

  CHECK_STATUS_OK(keymgr_testutils_disable(&keymgr));
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateDisabled));
  LOG_INFO("Keymgr entered Disabled state");

  return true;
}
