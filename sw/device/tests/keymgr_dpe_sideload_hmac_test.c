// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;

/**
 * TODO(#31206): Write test description
 */
static bool test_hmac_with_sideloaded_key(void) {
  // Generate the sideloaded key.
  dif_keymgr_dpe_generate_params_t sideload_params = kKeyVersionedParams;
  sideload_params.key_dest = kDifKeymgrDpeKeyDestHmac;
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

  // Generate the HMAC key
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(&keymgr_dpe, &sideload_params));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated HW output for HMAC from the CreatorRootKey");

  // TODO(#31206): Write a meaningful test for HMAC

  return true;
}

bool test_main(void) {
  // Start keymgr_dpe, generating CreatorRootKey into the slot defined by
  // kCreatorRootKeyParams(/sw/device/lib/testing/keymgr_dpe_testutils.h)
  CHECK_STATUS_OK(keymgr_dpe_testutils_startup(&keymgr_dpe, &kmac));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived CreatorRootKey and removed the UDS");
  LOG_INFO("KeymgrDpe is ready for the HMAC test!");

  // Run the HMAC test.
  return test_hmac_with_sideloaded_key();
}
