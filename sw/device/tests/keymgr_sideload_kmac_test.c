// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.
#include "kmac_regs.h"    // Generated.

// The KMAC dif expects a secret key, even though if the configuration is set
// to use the sideloaded key then it will be ignored. We will write a software
// key and then ensure that the output does NOT match the expected value for
// this key when sideloading is used.
//
// Test taken from sample #1 here:
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
static const dif_kmac_key_t kSoftwareKey = {
    .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C, 0x53525150,
               0x57565554, 0x5B5A5958, 0x5F5E5D5C},
    .share1 = {0},
    .length = kDifKmacKeyLen256,
};
static const dif_kmac_mode_kmac_t kKmacMode = kDifKmacModeKmacLen128;
static const size_t kKmacOutputLen = 8;
static const uint32_t kSoftwareKeyExpectedOutput[8] = {
    0x0D0B78E5, 0xD3F7A63E, 0x70C529A4, 0x003AA46A,
    0xD4D7DBFA, 0x9E832896, 0x3F248731, 0x4EE16E45};
static const char *kCustomString = NULL;
static const size_t kCustomStringLen = 0;
static const char kKmacMessage[] = "\x00\x01\x02\x03";
static const size_t kKmacMessageLen = 4;

// This is computed and filled by dv side
static volatile const uint8_t sideload_digest_result[32] = {0};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initialize and run KMAC using a sideloaded key.
 *
 * First, checks that KMAC works with the software key. Next, checks that when
 * sideload=true, KMAC produces a different result.
 */
static void test_kmac_with_sideloaded_key(dif_keymgr_t *keymgr,
                                          dif_kmac_t *kmac) {
  // Configure KMAC hardware (using software key and software entropy).
  kmac_testutils_config(kmac, false);

  uint32_t output[kKmacOutputLen];
  kmac_testutils_kmac(kmac, kKmacMode, &kSoftwareKey, kCustomString,
                      kCustomStringLen, kKmacMessage, kKmacMessageLen,
                      kKmacOutputLen, output);
  LOG_INFO("Computed KMAC output for software key.");

  // Check that the output matches the expected output.
  CHECK_ARRAYS_EQ(output, kSoftwareKeyExpectedOutput, kKmacOutputLen);

  // Reconfigure KMAC to use the sideloaded key.
  kmac_testutils_config(kmac, true);

  // Generate the sideloaded key.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;
  keymgr_testutils_generate_versioned_key(keymgr, sideload_params);
  LOG_INFO("Keymgr generated HW output for Kmac at OwnerIntKey State");

  kmac_testutils_kmac(kmac, kKmacMode, &kSoftwareKey, kCustomString,
                      kCustomStringLen, kKmacMessage, kKmacMessageLen,
                      kKmacOutputLen, output);
  LOG_INFO("Computed KMAC output for sideloaded key.");

  if (kDeviceType == kDeviceSimDV) {
    CHECK_ARRAYS_EQ(output, (uint32_t *)sideload_digest_result, kKmacOutputLen);
  }
}

bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  keymgr_testutils_startup(&keymgr, &kmac);

  // Advance to OwnerIntKey state.
  keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
  keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
  LOG_INFO("Keymgr entered OwnerIntKey State");

  // Test KMAC sideloading.
  test_kmac_with_sideloaded_key(&keymgr, &kmac);

  return true;
}
