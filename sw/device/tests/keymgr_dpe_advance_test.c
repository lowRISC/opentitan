// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/ip/keymgr_dpe/test/utils/keymgr_dpe_testutils.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/runtime/print.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "keymgr_dpe_regs.h"  // Generated.
#include "kmac_regs.h"        // Generated.

OTTF_DEFINE_TEST_CONFIG();

static void init_kmac_for_keymgr(void) {
  dif_kmac_t kmac;
  CHECK_DIF_OK(dif_kmac_init(
      mmio_region_from_addr(TOP_DARJEELING_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_fast_process = false,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .sideload = true,
      .msg_mask = true,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));
}

bool test_main(void) {
  // Initialize keymgr_dpe
  dif_keymgr_dpe_t keymgr_dpe;
  dif_keymgr_dpe_advance_params_t keymgr_dpe_advance_params;
  dif_keymgr_dpe_generate_params_t genparams;
  dif_keymgr_dpe_output_t key;

  CHECK_STATUS_OK(keymgr_dpe_testutils_startup(&keymgr_dpe));

  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  LOG_INFO("KeymgrDpe state available");

  keymgr_dpe_advance_params.slot_src_sel = 1;
  keymgr_dpe_advance_params.slot_dst_sel = 1;
  keymgr_dpe_advance_params.max_key_version = 0x100;
  keymgr_dpe_advance_params.binding_value[0] = 0xd;
  keymgr_dpe_advance_params.binding_value[1] = 0xe;
  keymgr_dpe_advance_params.binding_value[2] = 0xa;
  keymgr_dpe_advance_params.binding_value[3] = 0xd;
  keymgr_dpe_advance_params.binding_value[4] = 0xb;
  keymgr_dpe_advance_params.binding_value[5] = 0xe;
  keymgr_dpe_advance_params.binding_value[6] = 0xe;
  keymgr_dpe_advance_params.binding_value[7] = 0xf;
  keymgr_dpe_advance_params.slot_policy = 0x7;

  init_kmac_for_keymgr();

  CHECK_STATUS_OK(keymgr_dpe_testutils_advance_state(
      &keymgr_dpe, &keymgr_dpe_advance_params));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  LOG_INFO("KeymgrDpe updated UDS slot");

  CHECK_STATUS_OK(keymgr_dpe_testutils_wait_for_operation_done(&keymgr_dpe));

  keymgr_dpe_advance_params.slot_src_sel = 1;
  keymgr_dpe_advance_params.slot_dst_sel = 2;
  keymgr_dpe_advance_params.max_key_version = 0x100;
  keymgr_dpe_advance_params.binding_value[0] = 0xd;
  keymgr_dpe_advance_params.binding_value[1] = 0xe;
  keymgr_dpe_advance_params.binding_value[2] = 0xa;
  keymgr_dpe_advance_params.binding_value[3] = 0xd;
  keymgr_dpe_advance_params.binding_value[4] = 0xb;
  keymgr_dpe_advance_params.binding_value[5] = 0xe;
  keymgr_dpe_advance_params.binding_value[6] = 0xe;
  keymgr_dpe_advance_params.binding_value[7] = 0xf;
  keymgr_dpe_advance_params.slot_policy = 0x7;
  
  CHECK_STATUS_OK(keymgr_dpe_testutils_advance_state(
      &keymgr_dpe, &keymgr_dpe_advance_params));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  LOG_INFO("KeymgrDpe advanced to slot 2");
 
  CHECK_STATUS_OK(keymgr_dpe_testutils_wait_for_operation_done(&keymgr_dpe));

  genparams.key_dest = kDifKeymgrDpeKeyDestAes;
  genparams.sideload_key = false;
  genparams.salt[0] = 0xd;
  genparams.salt[1] = 0xe;
  genparams.salt[2] = 0xa;
  genparams.salt[3] = 0xd;
  genparams.salt[4] = 0xb;
  genparams.salt[5] = 0xe;
  genparams.salt[6] = 0xe;
  genparams.salt[7] = 0xf;
  genparams.version = 0;
  genparams.slot_src_sel = 2;

  CHECK_STATUS_OK(keymgr_dpe_testutils_generate(&keymgr_dpe, &genparams, &key));
  for (size_t i = 0; i < ARRAYSIZE(key.value); i++) {
	  for (size_t j = 0; j < ARRAYSIZE(key.value[0]); j++) {
		  LOG_INFO("KeymgrDpe generated key from slot 2 : %x ", key.value[i][j]);
	  }
  }

  keymgr_dpe_advance_params.slot_src_sel = 2;
  keymgr_dpe_advance_params.slot_dst_sel = 3;
  keymgr_dpe_advance_params.max_key_version = 0x100;
  keymgr_dpe_advance_params.binding_value[0] = 0xd;
  keymgr_dpe_advance_params.binding_value[1] = 0xe;
  keymgr_dpe_advance_params.binding_value[2] = 0xa;
  keymgr_dpe_advance_params.binding_value[3] = 0xd;
  keymgr_dpe_advance_params.binding_value[4] = 0xb;
  keymgr_dpe_advance_params.binding_value[5] = 0xe;
  keymgr_dpe_advance_params.binding_value[6] = 0xe;
  keymgr_dpe_advance_params.binding_value[7] = 0xf;
  keymgr_dpe_advance_params.slot_policy = 0x5;
  
  CHECK_STATUS_OK(keymgr_dpe_testutils_advance_state(
      &keymgr_dpe, &keymgr_dpe_advance_params));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  LOG_INFO("KeymgrDpe advanced to slot 3");

  genparams.key_dest = kDifKeymgrDpeKeyDestAes;
  genparams.sideload_key = false;
  genparams.salt[0] = 0xd;
  genparams.salt[1] = 0xe;
  genparams.salt[2] = 0xa;
  genparams.salt[3] = 0xd;
  genparams.salt[4] = 0xb;
  genparams.salt[5] = 0xe;
  genparams.salt[6] = 0xe;
  genparams.salt[7] = 0xf;
  genparams.version = 0;
  genparams.slot_src_sel = 3;

  CHECK_STATUS_OK(keymgr_dpe_testutils_generate(&keymgr_dpe, &genparams, &key));
  for (size_t i = 0; i < ARRAYSIZE(key.value); i++) {
	  for (size_t j = 0; j < ARRAYSIZE(key.value[0]); j++) {
		  LOG_INFO("KeymgrDpe generated key 1 from slot 3: %x ", key.value[i][j]);
	  }
  }
  
  genparams.key_dest = kDifKeymgrDpeKeyDestAes;
  genparams.sideload_key = false;
  genparams.salt[0] = 0xd;
  genparams.salt[1] = 0xe;
  genparams.salt[2] = 0xa;
  genparams.salt[3] = 0xd;
  genparams.salt[4] = 0xb;
  genparams.salt[5] = 0xe;
  genparams.salt[6] = 0xe;
  genparams.salt[7] = 0xf;
  genparams.version = 0;
  genparams.slot_src_sel = 3;

  CHECK_STATUS_OK(keymgr_dpe_testutils_generate(&keymgr_dpe, &genparams, &key));
  for (size_t i = 0; i < ARRAYSIZE(key.value); i++) {
	  for (size_t j = 0; j < ARRAYSIZE(key.value[0]); j++) {
		  LOG_INFO("KeymgrDpe generated key 2 from slot 3: %x ", key.value[i][j]);
	  }
  }

  return true;
}
