// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_keymgr_dpe.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;
static dif_otbn_t otbn;

static const dt_otbn_t kOtbnDt = (dt_otbn_t)0;

enum {
  // Last boot stage (`BootStageRuntime`). Advancing from it saturates.
  kKeymgrDpeBootStageRuntime = 4,
};

// OTBN application servicing the keymgr KDF interface. It receives the message
// and returns a fixed response that the host places in DMEM.
OTBN_DECLARE_APP_SYMBOLS(keymgr_test);
OTBN_DECLARE_SYMBOL_ADDR(keymgr_test, response_s0);
OTBN_DECLARE_SYMBOL_ADDR(keymgr_test, response_s1);
static const otbn_app_t kOtbnAppKeymgrTest = OTBN_APP_T_INIT(keymgr_test);
static const otbn_addr_t kOtbnResponseAddrS0 =
    OTBN_ADDR_T_INIT(keymgr_test, response_s0);
static const otbn_addr_t kOtbnResponseAddrS1 =
    OTBN_ADDR_T_INIT(keymgr_test, response_s1);

// Fixed response returned by the OTBN app (512 bits per share). The two shares
// and the lower / upper halves of each share all differ, so that a mix-up is
// detected.
static const uint8_t kOtbnResponseS0[64] = {
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,  //
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,  //
    0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78,  //
    0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0,  //
    0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe,  //
    0xfe, 0xed, 0xfa, 0xce, 0x0b, 0xad, 0xf0, 0x0d,  //
    0x13, 0x57, 0x9b, 0xdf, 0x02, 0x46, 0x8a, 0xce,  //
    0xec, 0xa8, 0x64, 0x20, 0xfd, 0xb9, 0x75, 0x31,  //
};
static const uint8_t kOtbnResponseS1[64] = {
    0xa5, 0x5a, 0xc3, 0x3c, 0x96, 0x69, 0xf0, 0x0f,  //
    0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,  //
    0x7e, 0x81, 0x6d, 0x92, 0x5c, 0xa3, 0x4b, 0xb4,  //
    0x3a, 0xc5, 0x29, 0xd6, 0x18, 0xe7, 0x07, 0xf8,  //
    0x55, 0xaa, 0x33, 0xcc, 0x66, 0x99, 0x0f, 0xf0,  //
    0x21, 0x43, 0x65, 0x87, 0xa9, 0xcb, 0xed, 0x0f,  //
    0xb1, 0x6b, 0x00, 0xb5, 0x5e, 0xed, 0xc0, 0xde,  //
    0x8b, 0xad, 0xf0, 0x0d, 0x1c, 0xe0, 0xc0, 0x1a,  //
};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Parameters for advancing a DPE context.
 */
static const dif_keymgr_dpe_advance_params_t kOtbnKdfDpeContext = {
    .binding_value = {0x3a9c5e71, 0x84d2f60b, 0x1e7ba493, 0xc5086f2d,
                      0x7f31d8e4, 0x29a6c057, 0xe40b937a, 0x5dc8126f},
    .max_key_version = 0x22,
    .slot_src_sel = kCreatorRootKeyParams.slot_dst_sel,
    .slot_dst_sel = kCreatorRootKeyParams.slot_dst_sel,
    .slot_policy = 9  // 0b1001 Allow children and keygen, erase the parent
};

/**
 * Parameters for generating a SW key from the derived DPE context.
 */
static const dif_keymgr_dpe_generate_params_t kOtbnKdfSwKeyParams = {
    .key_dest = kDifKeymgrDpeKeyDestNone,
    .sideload_key = false,
    .salt = {0x8c2e4f17, 0x53a9d06b, 0xe17b3c95, 0x0d64f2a8, 0x9f05b7c3,
             0x26d8e41a, 0xb3417f6e, 0x71ca90d2},
    .version = 0x1,
    .slot_src_sel = kOtbnKdfDpeContext.slot_dst_sel,
};

/**
 * Places the fixed response shares in DMEM and starts the OTBN app. The app
 * serves a single keymgr_dpe KDF request and then ends.
 */
static void otbn_kdf_app_start(dif_otbn_t *otbn) {
  CHECK_STATUS_OK(otbn_testutils_write_data(
      otbn, sizeof(kOtbnResponseS0), kOtbnResponseS0, kOtbnResponseAddrS0));
  CHECK_STATUS_OK(otbn_testutils_write_data(
      otbn, sizeof(kOtbnResponseS1), kOtbnResponseS1, kOtbnResponseAddrS1));
  CHECK_STATUS_OK(otbn_testutils_execute(otbn));
}

/**
 * Smoketest which uses OTBN as KDF engine.
 */
static void test_otbn_kdf(dif_keymgr_dpe_t *keymgr_dpe, dif_otbn_t *otbn) {
  // Record the boot stage of the parent context. With the ROM / ROM_EXT, the
  // parent is not necessarily the CreatorRootKey.
  dif_keymgr_dpe_metadata_t parent_metadata;
  CHECK_DIF_OK(dif_keymgr_dpe_get_metadata(
      keymgr_dpe, kOtbnKdfDpeContext.slot_src_sel, &parent_metadata));
  CHECK(parent_metadata.valid, "Parent DPE context is not valid");
  uint32_t exp_boot_stage =
      parent_metadata.boot_stage < kKeymgrDpeBootStageRuntime
          ? parent_metadata.boot_stage + 1
          : kKeymgrDpeBootStageRuntime;

  // Load the OTBN app and start it. It runs until the keymgr sends the message.
  CHECK_STATUS_OK(otbn_testutils_load_app(otbn, kOtbnAppKeymgrTest));
  otbn_kdf_app_start(otbn);

  // Switch the KDF engine from KMAC to OTBN.
  CHECK_DIF_OK(
      dif_keymgr_dpe_set_kdf_engine(keymgr_dpe, kDifKeymgrDpeKdfEngineOtbn));

  // Advance the DPE context using kOtbnKdfDpeContext.
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_advance_state(keymgr_dpe, &kOtbnKdfDpeContext));

  // Verify that OTBN finished and raised no error.
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));

  // Verify that the child context was derived with the expected metadata.
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_metadata(
      keymgr_dpe, kOtbnKdfDpeContext.slot_dst_sel,
      kOtbnKdfDpeContext.max_key_version, exp_boot_stage,
      kOtbnKdfDpeContext.slot_policy));
}

/**
 * Generates a SW key from the derived DPE context with OTBN as KDF engine and
 * checks the key against the response returned by the OTBN app.
 */
static void test_otbn_kdf_sw_key(dif_keymgr_dpe_t *keymgr_dpe,
                                 dif_otbn_t *otbn) {
  // Restart the OTBN app to serve the KDF request of the generate operation.
  otbn_kdf_app_start(otbn);

  // Generate a SW key. Only SW keys are written to the SW_SHARE*_OUTPUT
  // registers, sideload keys are not readable by SW.
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate_key(keymgr_dpe, &kOtbnKdfSwKeyParams));

  // Verify that OTBN finished and raised no error.
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(otbn, kDifOtbnErrBitsNoError));

  // keymgr_dpe outputs the lower 256 bits of each digest share, so output
  // share 0 / 1 must match the first 32 bytes of kOtbnResponseS0 / S1.
  dif_keymgr_dpe_output_t key;
  CHECK_DIF_OK(dif_keymgr_dpe_read_output(keymgr_dpe, &key));
  CHECK_ARRAYS_EQ((const uint8_t *)key.value[0], kOtbnResponseS0,
                  sizeof(key.value[0]));
  CHECK_ARRAYS_EQ((const uint8_t *)key.value[1], kOtbnResponseS1,
                  sizeof(key.value[1]));
}

bool test_main(void) {
  // Start keymgr_dpe, generating CreatorRootKey into the slot defined by
  // kCreatorRootKeyParams(/sw/device/lib/testing/keymgr_dpe_testutils.h)
  CHECK_STATUS_OK(keymgr_dpe_testutils_startup(&keymgr_dpe, &kmac));
  CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(
      &keymgr_dpe, kDifKeymgrDpeStateAvailable));
  // Initialize OTBN.
  CHECK_DIF_OK(dif_otbn_init_from_dt(kOtbnDt, &otbn));
  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived CreatorRootKey and removed the UDS");

  // Derive a DPE context using the OTBN as KDF (HKDF).
  test_otbn_kdf(&keymgr_dpe, &otbn);

  // DV SYNC MESSAGE
  LOG_INFO("KeymgrDpe derived DPE context with the OTBN (HKDF)");

  // Generate a SW key from the derived DPE context using the OTBN as KDF.
  test_otbn_kdf_sw_key(&keymgr_dpe, &otbn);
  LOG_INFO("KeymgrDpe generated SW key with the OTBN (HKDF)");

  return true;
}
