// Copyright lowRISC contributors (OpenTitan project).
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

static dif_keymgr_t keymgr;
static dif_kmac_t kmac;

// This is computed and filled by dv side
static volatile const uint8_t sideload_digest_result[32] = {0};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles(void) {
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
}

/**
 * Compute the total length of capacity.
 *
 * The length of the capacity is either 256 or 512 depending on the security
 * strength implied by `kmac_mode`. The total length of capacity refers to
 * the length of concatenated capacity parts across multiple output Keccak
 * rounds. For instance, if `kmac_mode` implies 128-bit security and if
 * `digest_len` implies 336 bytes of digest, then the total capacity is 512
 * bits.
 *
 * @param kmac_mode KMAC mode that implies security strength.
 * @param digest_len The length of the requested digest from KMAC operation in
 * words.
 * @param[out] capacity_total_len The total length of multiple capacity blocks
 * in words.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static status_t get_total_capacity_len(dif_kmac_mode_kmac_t kmac_mode,
                                       size_t digest_len,
                                       size_t *capacity_total_len) {
  size_t capacity_len;
  size_t rate_len;
  if (kmac_mode == kDifKmacModeKmacLen128) {
    capacity_len = 256 / 8 / sizeof(uint32_t);
  } else if (kmac_mode == kDifKmacModeKmacLen256) {
    capacity_len = 512 / 8 / sizeof(uint32_t);
  } else {
    return INVALID_ARGUMENT();
  }
  rate_len = kDifKmacStateWords - capacity_len;
  *capacity_total_len = ceil_div(digest_len, rate_len) * capacity_len;
  return OK_STATUS();
}

/**
 * Initialize and run KMAC using a sideloaded key.
 *
 * First, checks that KMAC works with the software key. Next, checks that when
 * sideload=true, KMAC produces a different result.
 */
static void test_kmac_with_sideloaded_key(dif_keymgr_t *keymgr,
                                          dif_kmac_t *kmac) {
  // Configure KMAC hardware (using software key and software entropy).
  CHECK_STATUS_OK(kmac_testutils_config(kmac, false));

  // Allocate buffers to read capacity into so that we can test if it is
  // zeroized for sideloaded KMAC operations (see #17759).
  size_t capacity_total_len;
  CHECK_STATUS_OK(
      get_total_capacity_len(kKmacMode, kKmacOutputLen, &capacity_total_len));
  uint32_t capacity[capacity_total_len];
  uint32_t zero_array[capacity_total_len];
  memset(zero_array, 0, sizeof(zero_array));
  // The expected capacity after SW-keyed KMAC is non-zero, so initialize the
  // array to 0.
  memset(capacity, 0, sizeof(capacity));

  uint32_t output[kKmacOutputLen];
  CHECK_STATUS_OK(kmac_testutils_kmac(
      kmac, kKmacMode, &kSoftwareKey, kCustomString, kCustomStringLen,
      kKmacMessage, kKmacMessageLen, kKmacOutputLen, output, capacity));
  LOG_INFO("Computed KMAC output for software key.");

  // Check that the output matches the expected output.
  CHECK_ARRAYS_EQ(output, kSoftwareKeyExpectedOutput, kKmacOutputLen);

  // Check that the capacity part is non-zero
  CHECK_ARRAYS_NE(capacity, zero_array, ARRAYSIZE(capacity));

  // Reconfigure KMAC to use the sideloaded key.
  CHECK_STATUS_OK(kmac_testutils_config(kmac, true));

  // Generate the sideloaded key.
  dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
  sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;

  // Get the maximum key version supported by the keymgr in its current state.
  uint32_t max_key_version;
  CHECK_STATUS_OK(
      keymgr_testutils_max_key_version_get(keymgr, &max_key_version));

  if (sideload_params.version > max_key_version) {
    LOG_INFO("Key version %d is greater than the maximum key version %d",
             sideload_params.version, max_key_version);
    LOG_INFO("Setting key version to the maximum key version %d",
             max_key_version);
    sideload_params.version = max_key_version;
  }

  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
  LOG_INFO("Keymgr generated HW output for Kmac at OwnerIntKey State");

  uint32_t output_sideload_good0[kKmacOutputLen];
  CHECK_STATUS_OK(
      kmac_testutils_kmac(kmac, kKmacMode, &kSoftwareKey, kCustomString,
                          kCustomStringLen, kKmacMessage, kKmacMessageLen,
                          kKmacOutputLen, output_sideload_good0, capacity));
  LOG_INFO("Computed KMAC output for sideloaded key.");

  // Check that capacity is read as 0.
  CHECK_ARRAYS_EQ(capacity, zero_array, ARRAYSIZE(capacity));

  if (kDeviceType == kDeviceSimDV) {
    // From the DV environment we get the expected digest, so check that the
    // output using the sideloaded key matches the expectation.  We cannot do
    // this check outside the DV environment because we cannot observe the
    // sideloaded key, thus cannot compute the expected digest.
    CHECK_ARRAYS_EQ(output_sideload_good0, (uint32_t *)sideload_digest_result,
                    kKmacOutputLen);
  }

  LOG_INFO("Clearing the sideloaded key.");

  // Enable "clear the key" toggle, so that previous sideload key port is
  // cleared.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleEnabled));

  // Disable "clear the key" toggle, so that the sideload key port is stable.
  // Otherwise, the sideload port is continuously overwritten by fresh
  // randomness every clock cycle.
  CHECK_DIF_OK(
      dif_keymgr_sideload_clear_set_enabled(keymgr, kDifToggleDisabled));

  uint32_t output_sideload_bad[kKmacOutputLen];
  // Initialize this output array because the following `kmac_testutils_kmac`
  // function call fails early and is expected to *not* overwrite this array.
  for (size_t i = 0; i < kKmacOutputLen; i++) {
    output_sideload_bad[i] = i;
  }
  CHECK(kFailedPrecondition ==
        status_err(kmac_testutils_kmac(
            kmac, kKmacMode, &kSoftwareKey, kCustomString, kCustomStringLen,
            kKmacMessage, kKmacMessageLen, kKmacOutputLen, output_sideload_bad,
            /*capacity=*/NULL)));
  LOG_INFO("Ran KMAC with an invalid sideload key and checked that it fails.");

  // Verify that the output array did not get overwritten.
  for (size_t i = 0; i < kKmacOutputLen; i++) {
    CHECK(output_sideload_bad[i] == i);
  }

  // Sideload the same KMAC key again and check if we can compute the same
  // result as before.
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
  LOG_INFO("Keymgr regenerated HW output for Kmac at OwnerIntKey State");

  uint32_t output_sideload_good1[kKmacOutputLen];
  CHECK_STATUS_OK(kmac_testutils_kmac(
      kmac, kKmacMode, &kSoftwareKey, kCustomString, kCustomStringLen,
      kKmacMessage, kKmacMessageLen, kKmacOutputLen, output_sideload_good1,
      /*capacity=*/NULL));
  LOG_INFO("Re-computed KMAC output for sideloaded key.");

  CHECK_ARRAYS_EQ(output_sideload_good1, output_sideload_good0, kKmacOutputLen);
}

bool test_main(void) {
  init_peripheral_handles();

  CHECK_STATUS_OK(keymgr_testutils_initialize(&keymgr, &kmac));

  // Test KMAC sideloading.
  test_kmac_with_sideloaded_key(&keymgr, &kmac);
  return true;
}
