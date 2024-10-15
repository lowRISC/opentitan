// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/ret_sram_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
static const dif_kmac_mode_kmac_t kKmacModes[2] = {kDifKmacModeKmacLen128,
                                                   kDifKmacModeKmacLen256};
static const size_t kKmacOutputLen = 8;
static const char *kCustomString = NULL;
static const size_t kCustomStringLen = 0;
static const char kKmacMessage[] = "\x00\x01\x02\x03";
static const size_t kKmacMessageLen = 4;

enum {
  /**
   * Retention SRAM start address (inclusive).
   */
  kRetSramBaseAddr = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,

  kRetSramOwnerAddr = kRetSramBaseAddr + offsetof(retention_sram_t, owner),
  kRetRamLastAddr =
      kRetSramBaseAddr + TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES - 1,
};

static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_sram_ctrl_t ret_sram;
static dif_rstmgr_t rstmgr;

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initializes all DIF handles for each peripheral used in this test.
 */
static void init_peripheral_handles(void) {
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  CHECK_DIF_OK(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR),
      &ret_sram));
}

/**
 * KMAC key sideload test.
 *
 * This function is executed twice.
 *
 * In phase 0, KMAC outputs for kDifKmacModeKmacLen128 and
 * kDifKmacModeKmacLen256 with a sideloaded key are computed. The outputs are
 * stored in the retention SRAM to preserve the results. Then, the sideload key
 * is invalidated, a new sideload key with a different salt is generated and the
 * test checks whether KMAC can no longer reproduce the same KMAC output.
 *
 * Then, test_main performs a software reset.
 *
 * In phase 1, KMAC outputs for kDifKmacModeKmacLen128 and
 * kDifKmacModeKmacLen256 with a sideloaded key are computed. The outputs are
 * compared to the previous value stored in the retention SRAM.
 *
 * @param keymgr the key manager handle.
 * @param kmac the kmac handle.
 * @param test_phase the current test phase.
 */
static void test_kmac_key_sideload(dif_keymgr_t *keymgr, dif_kmac_t *kmac,
                                   size_t test_phase) {
  // Configure KMAC to use the sideloaded key.
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
  LOG_INFO("Keymgr generated HW output for Kmac");
  uint32_t output_sideload[ARRAYSIZE(kKmacModes)][kKmacOutputLen];

  for (size_t it = 0; it < ARRAYSIZE(kKmacModes); it++) {
    CHECK_STATUS_OK(kmac_testutils_kmac(
        kmac, kKmacModes[it], &kSoftwareKey, kCustomString, kCustomStringLen,
        kKmacMessage, kKmacMessageLen, kKmacOutputLen, output_sideload[it],
        /*capacity=*/NULL));
  }
  LOG_INFO("Computed KMAC output for sideloaded key.");

  if (!test_phase) {
    // In test phase 0, store the KMAC digest into the retention SRAM.
    for (size_t it = 0; it < ARRAYSIZE(kKmacModes); it++) {
      // Use kRetSramOwnerAddr + 4 to avoid overwriting test_phase_cnt.
      sram_ctrl_testutils_write(
          kRetSramOwnerAddr + 4 + 4 * it * kKmacOutputLen,
          (sram_ctrl_testutils_data_t){.words = output_sideload[it],
                                       .len = kKmacOutputLen});
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

    // Let the keymanager generate a new key with a different salt.
    sideload_params.salt[0] = ~sideload_params.salt[0];
    CHECK_STATUS_OK(
        keymgr_testutils_generate_versioned_key(keymgr, sideload_params));
    LOG_INFO("Keymgr generated new HW output for Kmac.");

    uint32_t output_sideload_after_clear[kKmacOutputLen];
    CHECK_STATUS_OK(
        kmac_testutils_kmac(kmac, kKmacModes[0], &kSoftwareKey, kCustomString,
                            kCustomStringLen, kKmacMessage, kKmacMessageLen,
                            kKmacOutputLen, output_sideload_after_clear,
                            /*capacity=*/NULL));
    LOG_INFO(
        "Ran KMAC with an another sideload key and checked that the output is "
        "not identical to before.");

    CHECK_ARRAYS_NE(output_sideload_after_clear, output_sideload[0],
                    kKmacOutputLen);

  } else {
    // In test phase 1, read the previous KMAC digests from the retention SRAM
    // and compare them with the calculated ones.
    for (size_t it = 0; it < ARRAYSIZE(kKmacModes); it++) {
      uint32_t prev_digest[kKmacOutputLen];
      memcpy(prev_digest,
             (uint8_t *)(kRetSramOwnerAddr + 4 + 4 * it * kKmacOutputLen),
             sizeof(prev_digest));
      CHECK_ARRAYS_EQ(output_sideload[it], prev_digest, kKmacOutputLen);
    }
    LOG_INFO("Checked current and previous KMAC digest.");
  }
}

bool test_main(void) {
  // Use the retention SRAM to store a test phase counter.
  const dif_rstmgr_reset_info_bitfield_t reset_info =
      rstmgr_testutils_reason_get();
  size_t test_phase_cnt;

  if (reset_info == kDifRstmgrResetInfoPor) {
    // Init counter to 0 after first power up.
    CHECK_STATUS_OK(ret_sram_testutils_counter_clear(0));
  }
  CHECK_STATUS_OK(ret_sram_testutils_counter_get(0, &test_phase_cnt));

  // Initialize peripherals and the keymanager.
  init_peripheral_handles();
  CHECK_STATUS_OK(keymgr_testutils_initialize(&keymgr, &kmac));

  LOG_INFO("Starting test phase %d", test_phase_cnt);
  test_kmac_key_sideload(&keymgr, &kmac, test_phase_cnt);
  LOG_INFO("Finished test phase %x", test_phase_cnt);

  // After phase 0, trigger a software reset.
  if (test_phase_cnt == 0) {
    CHECK_STATUS_OK(ret_sram_testutils_counter_increment(0));
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  }

  return true;
}
