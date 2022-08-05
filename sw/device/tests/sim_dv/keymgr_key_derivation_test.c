// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.
#include "kmac_regs.h"    // Generated.

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  keymgr_testutils_startup(&keymgr, &kmac);

  keymgr_testutils_generate_identity(&keymgr);
  LOG_INFO("Keymgr generated identity at CreatorRootKey State");

  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  keymgr_testutils_generate_identity(&keymgr);
  LOG_INFO("Keymgr generated identity at OwnerIntKey State");

  keymgr_testutils_generate_versioned_key(&keymgr, kKeyVersionedParams);
  LOG_INFO("Keymgr generated SW output at OwnerIntKey State");

  // Generate sideload keys for 3 HW interfaces - Kmac, Aes, Otbn.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;
  keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Kmac at OwnerIntKey State");

  sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
  keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Aes at OwnerIntKey State");

  sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
  keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Otbn at OwnerIntKey State");

  keymgr_testutils_disable(&keymgr);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateDisabled);
  LOG_INFO("Keymgr entered Disabled state");

  return true;
}
