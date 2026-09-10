// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/kmac.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_kmac_t kmac;
static dif_keymgr_dpe_t keymgr_dpe;

// Perform an advance operation with the given parameters and check if the
// keymgr dpe state is correct.
void advance(dif_keymgr_dpe_advance_params_t *params) {
  CHECK_STATUS_OK(keymgr_dpe_testutils_advance_state(&keymgr_dpe, params));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
}

// Perform a generate operation with the given parameters.
void generate(dif_keymgr_dpe_generate_params_t *params) {
  CHECK_STATUS_OK(keymgr_dpe_testutils_generate_key(&keymgr_dpe, params));
}

bool key_derivation_test(void) {
  dif_keymgr_dpe_advance_params_t adv_params;
  dif_keymgr_dpe_generate_params_t gen_params;

  // Generate OTBN output from the CreatorRootKey.
  gen_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  gen_params.version = 0;
  gen_params.salt[7] = 0x49379059;
  gen_params.salt[6] = 0xff523992;
  gen_params.salt[5] = 0x75666880;
  gen_params.salt[4] = 0xc0e44716;
  gen_params.salt[3] = 0x999612df;
  gen_params.salt[2] = 0x80f1a9de;
  gen_params.salt[1] = 0x481eae40;
  gen_params.salt[0] = 0x45e2c7f0;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated OTBN output from CreatorRootKey");

  // Generate SW output from the CreatorRootKey.
  gen_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;
  gen_params.sideload_key = false;  // SW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestNone;
  gen_params.version = 0;
  gen_params.salt[7] = 0x72d5886b;
  gen_params.salt[6] = 0x4e359e52;
  gen_params.salt[5] = 0x0d7ff336;
  gen_params.salt[4] = 0x267773cf;
  gen_params.salt[3] = 0x00c7d10c;
  gen_params.salt[2] = 0x6dea4fb9;
  gen_params.salt[1] = 0x77fa328a;
  gen_params.salt[0] = 0x15779805;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated SW output from CreatorRootKey");

  // Generate KMAC output the from CreatorRootKey.
  gen_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestKmac;
  gen_params.version = 0;
  gen_params.salt[7] = 0x78ad5715;
  gen_params.salt[6] = 0x508680d4;
  gen_params.salt[5] = 0xc7f825b2;
  gen_params.salt[4] = 0xa7924b8d;
  gen_params.salt[3] = 0x0906825f;
  gen_params.salt[2] = 0x77cf81a3;
  gen_params.salt[1] = 0xd63d89bd;
  gen_params.salt[0] = 0x88fd3697;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated KMAC output from CreatorRootKey");

  // Generate AES output from the from CreatorRootKey.
  gen_params.slot_src_sel = kCreatorRootKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestAes;
  gen_params.version = 0;
  gen_params.salt[7] = 0x945642d9;
  gen_params.salt[6] = 0xfbcbc925;
  gen_params.salt[5] = 0xdb7b0691;
  gen_params.salt[4] = 0xcd973f4d;
  gen_params.salt[3] = 0x278e051d;
  gen_params.salt[2] = 0x0d9f1f0d;
  gen_params.salt[1] = 0x45eff95b;
  gen_params.salt[0] = 0xb1ad6ba7;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated AES output from CreatorRootKey");

  // Advance the DPE context with the parameter defined in kOwnerIntKeyParams
  // (/sw/device/lib/testing/keymgr_dpe_testutils.h)
  adv_params.slot_src_sel = kOwnerIntKeyParams.slot_src_sel;
  adv_params.slot_dst_sel = kOwnerIntKeyParams.slot_dst_sel;
  adv_params.max_key_version = kOwnerIntKeyParams.max_key_version;
  for (uint32_t i = 0; i < 8; i++) {
    adv_params.binding_value[i] = kOwnerIntKeyParams.binding_value[i];
  }
  adv_params.slot_policy = kOwnerIntKeyParams.slot_policy;
  advance(&adv_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived OwnerIntKey");

  // Generate KMAC output from the OwnerIntKey key.
  gen_params.slot_src_sel = kOwnerIntKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestKmac;
  gen_params.version = 0;
  gen_params.salt[7] = 0x6b21d5da;
  gen_params.salt[6] = 0x929ea4f4;
  gen_params.salt[5] = 0xeb06038b;
  gen_params.salt[4] = 0xcecba4ea;
  gen_params.salt[3] = 0x8c8e756a;
  gen_params.salt[2] = 0x26691553;
  gen_params.salt[1] = 0x7189202b;
  gen_params.salt[0] = 0x5e560c86;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated KMAC output from OwnerIntKey");

  // Generate AES output from the OwnerIntKey.
  gen_params.slot_src_sel = kOwnerIntKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestAes;
  gen_params.version = 1;
  gen_params.salt[7] = 0xcd887c60;
  gen_params.salt[6] = 0xcc40f919;
  gen_params.salt[5] = 0xdd2972b7;
  gen_params.salt[4] = 0x09cdc35f;
  gen_params.salt[3] = 0x3a10980c;
  gen_params.salt[2] = 0x4b38fdec;
  gen_params.salt[1] = 0x3d56d980;
  gen_params.salt[0] = 0x25314e07;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated AES output from OwnerIntKey");

  // Generate SW output from the OwnerIntKey.
  gen_params.slot_src_sel = kOwnerIntKeyParams.slot_dst_sel;
  gen_params.sideload_key = false;  // SW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestNone;
  gen_params.version = 2;
  gen_params.salt[7] = 0x72d5886b;
  gen_params.salt[6] = 0x4e359e52;
  gen_params.salt[5] = 0x0d7ff336;
  gen_params.salt[4] = 0x267773cf;
  gen_params.salt[3] = 0x00c7d10c;
  gen_params.salt[2] = 0x6dea4fb9;
  gen_params.salt[1] = 0x77fa328a;
  gen_params.salt[0] = 0x15779805;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated SW output from OwnerIntKey");

  // Generate OTBN output from the OwnerIntKey.
  gen_params.slot_src_sel = kOwnerIntKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  gen_params.version = 3;
  gen_params.salt[7] = 0x564712d4;
  gen_params.salt[6] = 0x7ab745f5;
  gen_params.salt[5] = 0x5fa8faa9;
  gen_params.salt[4] = 0x77fce728;
  gen_params.salt[3] = 0xffa3fd3c;
  gen_params.salt[2] = 0x876930f2;
  gen_params.salt[1] = 0x593b54d4;
  gen_params.salt[0] = 0xa75e231b;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated OTBN output from OwnerIntKey");

  // Advance the DPE context with the parameter defined in kOwnerKeyParams
  // (/sw/device/lib/testing/keymgr_dpe_testutils.h)
  adv_params.slot_src_sel = kOwnerKeyParams.slot_src_sel;
  adv_params.slot_dst_sel = kOwnerKeyParams.slot_dst_sel;
  adv_params.max_key_version = kOwnerKeyParams.max_key_version;
  for (uint32_t i = 0; i < 8; i++) {
    adv_params.binding_value[i] = kOwnerKeyParams.binding_value[i];
  }
  adv_params.slot_policy = kOwnerKeyParams.slot_policy;
  advance(&adv_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived OwnerKey");

  // Generate SW output from the OwnerKey.
  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = false;  // SW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestNone;
  gen_params.version = 0;
  gen_params.salt[7] = 0xe1b3f29c;
  gen_params.salt[6] = 0xa3bc4d2a;
  gen_params.salt[5] = 0x458fdc76;
  gen_params.salt[4] = 0x1b1c0c2e;
  gen_params.salt[3] = 0x1a128785;
  gen_params.salt[2] = 0x69ce2d2f;
  gen_params.salt[1] = 0x8a60fd60;
  gen_params.salt[0] = 0x5307745c;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated SW output from OwnerKey");

  dif_keymgr_dpe_output_t key;
  LOG_INFO("KeymgrDpe read the generated SW out");
  CHECK_DIF_OK(dif_keymgr_dpe_read_output(&keymgr_dpe, &key));
  for (size_t i = 0; i < ARRAYSIZE(key.value); i++) {
    for (size_t j = 0; j < ARRAYSIZE(key.value[0]); j++) {
      LOG_INFO("%x ", key.value[i][j]);
    }
  }

  // Generate AES output from the OwnerKey.
  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestAes;
  gen_params.version = 1;
  gen_params.salt[7] = 0x0f20f37e;
  gen_params.salt[6] = 0xb951b619;
  gen_params.salt[5] = 0xcb815e8d;
  gen_params.salt[4] = 0x77e17fa4;
  gen_params.salt[3] = 0x3074e3db;
  gen_params.salt[2] = 0xe7482b04;
  gen_params.salt[1] = 0xed12d4ee;
  gen_params.salt[0] = 0xa34fba3c;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated AES output from OwnerKey");

  // Generate KMAC output from the OwnerKey.
  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestKmac;
  gen_params.version = 2;
  gen_params.salt[7] = 0xb31031a3;
  gen_params.salt[6] = 0x59fe6e8e;
  gen_params.salt[5] = 0x4171de6b;
  gen_params.salt[4] = 0xa3f3d397;
  gen_params.salt[3] = 0x7bb7800b;
  gen_params.salt[2] = 0x8f8f8cda;
  gen_params.salt[1] = 0xb697609d;
  gen_params.salt[0] = 0x122eb3b7;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated KMAC output from OwnerKey");

  // Generate OTBN output from the OwnerKey.
  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  gen_params.version = 3;
  gen_params.salt[7] = 0x3f184f9b;
  gen_params.salt[6] = 0xd4af6765;
  gen_params.salt[5] = 0x8abeb221;
  gen_params.salt[4] = 0xaae3ca52;
  gen_params.salt[3] = 0x29f7114f;
  gen_params.salt[2] = 0xf5bf3e01;
  gen_params.salt[1] = 0x6a961bc2;
  gen_params.salt[0] = 0xec932d64;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated OTBN output from OwnerKey");

  // Derive a DPE context from the OwnerKey without overwriting the
  // OwnerKey.
  adv_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  adv_params.slot_dst_sel = 3;
  adv_params.binding_value[7] = 0x952b5a35;
  adv_params.binding_value[6] = 0x28b4520e;
  adv_params.binding_value[5] = 0x1f310db2;
  adv_params.binding_value[4] = 0x832b8477;
  adv_params.binding_value[3] = 0x75b81191;
  adv_params.binding_value[2] = 0x0668dc27;
  adv_params.binding_value[1] = 0xa226160d;
  adv_params.binding_value[0] = 0x45790409;
  adv_params.max_key_version = 0x100;
  // Children allowed without retaining the partent slot
  adv_params.slot_policy = 1;
  // Generate a new (derived from OwnerKey) DPE context
  advance(&adv_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived new DPE context from OwnerKey");

  // Generate AES output from the boot stage 3 key.
  gen_params.slot_src_sel = 3;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestAes;
  gen_params.version = 0x10;
  gen_params.salt[7] = 0x30059d96;
  gen_params.salt[6] = 0x97436d9c;
  gen_params.salt[5] = 0xf539a20a;
  gen_params.salt[4] = 0x6838564e;
  gen_params.salt[3] = 0x74ad4bb7;
  gen_params.salt[2] = 0x78000277;
  gen_params.salt[1] = 0x423025af;
  gen_params.salt[0] = 0x732e53a9;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated AES output from DPE context in slot %0d",
           adv_params.slot_dst_sel);

  // Generate OTBN output from the boot stage 3 key.
  gen_params.slot_src_sel = 3;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  gen_params.version = 0x20;
  gen_params.salt[7] = 0x2cd82d66;
  gen_params.salt[6] = 0x24275e98;
  gen_params.salt[5] = 0xe0344ab2;
  gen_params.salt[4] = 0xc048d59e;
  gen_params.salt[3] = 0x139694c3;
  gen_params.salt[2] = 0x0043f9b4;
  gen_params.salt[1] = 0x413a2212;
  gen_params.salt[0] = 0xc2dcfbc8;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated OTBN output from DPE context in slot %0d",
           adv_params.slot_dst_sel);

  // Generate SW output from the boot stage 3 key.
  gen_params.slot_src_sel = 3;
  gen_params.sideload_key = false;  // SW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestNone;
  gen_params.version = 0x30;
  gen_params.salt[7] = 0x23c20696;
  gen_params.salt[6] = 0xebaf62f0;
  gen_params.salt[5] = 0xa2ff413f;
  gen_params.salt[4] = 0x22d65603;
  gen_params.salt[3] = 0x91155c24;
  gen_params.salt[2] = 0xda1269fc;
  gen_params.salt[1] = 0xc8611986;
  gen_params.salt[0] = 0xf129041f;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated SW output from DPE context in slot %0d",
           adv_params.slot_dst_sel);

  // Generate KMAC output from the boot stage 3 key.
  gen_params.slot_src_sel = 3;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestKmac;
  gen_params.version = 0x40;
  gen_params.salt[7] = 0x06896da3;
  gen_params.salt[6] = 0x9ce2c0da;
  gen_params.salt[5] = 0xaa23a965;
  gen_params.salt[4] = 0x108e57ca;
  gen_params.salt[3] = 0xd926d474;
  gen_params.salt[2] = 0xb6ae40fc;
  gen_params.salt[1] = 0xa65d1375;
  gen_params.salt[0] = 0x6ee7be64;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated KMAC output from DPE context in slot %0d",
           adv_params.slot_dst_sel);

  // Generate some additional outputs from the owner root keys, which
  // should still be available.
  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = false;  // SW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestNone;
  gen_params.version = 42;
  gen_params.salt[7] = 0x2488d617;
  gen_params.salt[6] = 0x99227306;
  gen_params.salt[5] = 0xcd789bc0;
  gen_params.salt[4] = 0x9787039b;
  gen_params.salt[3] = 0x9869544a;
  gen_params.salt[2] = 0xb28b9fc7;
  gen_params.salt[1] = 0x69ab6f9d;
  gen_params.salt[0] = 0xfb11f188;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated SW output from OwnerKey");

  gen_params.slot_src_sel = kOwnerKeyParams.slot_dst_sel;
  gen_params.sideload_key = true;  // HW key
  gen_params.key_dest = kDifKeymgrDpeKeyDestOtbn;
  gen_params.version = 7;
  gen_params.salt[7] = 0xfa94162c;
  gen_params.salt[6] = 0xd039a40f;
  gen_params.salt[5] = 0xc2b81d98;
  gen_params.salt[4] = 0x999ce18d;
  gen_params.salt[3] = 0xbf8fb838;
  gen_params.salt[2] = 0x589544ce;
  gen_params.salt[1] = 0xee7790c4;
  gen_params.salt[0] = 0x0de6bdcf;
  generate(&gen_params);
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe generated OTBN output from OwnerKey");

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

  // run the specific test sequence with CreatorRootKey
  return key_derivation_test();
}
