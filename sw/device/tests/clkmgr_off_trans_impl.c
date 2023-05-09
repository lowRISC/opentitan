// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/clkmgr_off_trans_impl.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * The hints bit order is
 * bit 0: AES
 * bit 1: HMAC
 * bit 2: KMAC
 * bit 3: OTBN
 */

OTTF_DEFINE_TEST_CONFIG();

static dif_aon_timer_t aon_timer;

static dif_aes_t aes;
static dif_hmac_t hmac;
static dif_kmac_t kmac;
static dif_otbn_t otbn;

static const uint32_t bite_us = 400;

/**
 * Send CSR access to aes, expecting to timeout.
 */
static void aes_csr_access(void) {
  bool status;
  CHECK_DIF_OK(dif_aes_get_status(&aes, kDifAesStatusIdle, &status));
}

static void hmac_csr_access(void) {
  uint32_t num_entries;
  CHECK_DIF_OK(dif_hmac_fifo_count_entries(&hmac, &num_entries));
}

static void kmac_csr_access(void) {
  dif_kmac_status_t status;
  CHECK_DIF_OK(dif_kmac_get_status(&kmac, &status));
}

static void otbn_csr_access(void) {
  dif_otbn_err_bits_t err_bits;
  CHECK_DIF_OK(dif_otbn_get_err_bits(&otbn, &err_bits));
}

static void trans_csr_access(dif_clkmgr_hintable_clock_t trans) {
  switch (trans) {
    case kTopEarlgreyHintableClocksMainAes:
      aes_csr_access();
      break;
    case kTopEarlgreyHintableClocksMainHmac:
      hmac_csr_access();
      break;
    case kTopEarlgreyHintableClocksMainKmac:
      kmac_csr_access();
      break;
    case kTopEarlgreyHintableClocksMainOtbn:
      otbn_csr_access();
      break;
    default:
      LOG_ERROR("Invalid hintable clock (%d)", trans);
      break;
  }
}

/**
 * Test that disabling a 'hintable' unit's clock causes the unit to become
 * unresponsive to CSR accesses. Configure a watchdog reset, and if it triggers
 * the test is successful.
 */
static void test_hintable_clocks_off(const dif_clkmgr_t *clkmgr,
                                     dif_clkmgr_hintable_clock_t clock) {
  // Make sure the clock for the unit is on.
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, kDifToggleEnabled));

  // The unit is enabled. Set the aon timer to bite, disable it, and issue a
  // CSR read.
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(bite_us, &bite_cycles));
  LOG_INFO("Setting bite reset for %u us (%u cycles)", bite_us, bite_cycles);

  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX,
                                                      bite_cycles, false));
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_set_hint(clkmgr, clock, kDifToggleDisabled));
  // Short wait to make sure clocks reacted to hints.
  busy_spin_micros(1);
  // Check all units but the hinted one are alive.
  for (dif_clkmgr_hintable_clock_t other = 0;
       other <= kTopEarlgreyHintableClocksLast; ++other) {
    if (other != clock) {
      trans_csr_access(other);
    }
  }
  LOG_INFO("All other units are alive");
  trans_csr_access(clock);
  LOG_ERROR("Access to disabled unit should freeze and cause a reset");
}

bool execute_off_trans_test(dif_clkmgr_hintable_clock_t clock) {
  dif_clkmgr_t clkmgr;
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize aon timer.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // Initialize aes.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));

  // Initialize hmac.
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));

  // Initialize kmac.
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Initialize otbn.
  CHECK_DIF_OK(
      dif_otbn_init(mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR), &otbn));

  // Enable cpu dump capture.
  CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    // Enable watchdog bite reset.
    CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeReset,
                                                kDifPwrmgrResetRequestSourceTwo,
                                                kDifToggleEnabled));
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    test_hintable_clocks_off(&clkmgr, clock);

    // This should never be reached.
    LOG_ERROR("This is unreachable since a reset should have been triggered");
    return false;
  } else if (UNWRAP(rstmgr_testutils_is_reset_info(
                 &rstmgr, kDifRstmgrResetInfoWatchdog))) {
    // Verify the cpu crash dump.
    LOG_INFO("Got an expected watchdog reset when reading for clock %d", clock);
    // TODO: Enable reading the CPU dump once the following issue is resolved
    // (https://github.com/lowRISC/opentitan/issues/13022)
    /*
    dif_rstmgr_cpu_info_dump_segment_t cpu_dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
    size_t size_read;
    CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
        &rstmgr, cpu_dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
    LOG_INFO("Read cpu dump");
    CHECK(size_read == DIF_RSTMGR_CPU_INFO_MAX_SIZE);
    LOG_INFO("PC           = 0x%x", cpu_dump[0]);
    LOG_INFO("NEXT PC      = 0x%x", cpu_dump[1]);
    LOG_INFO("DATA ADDRESS = 0x%x", cpu_dump[2]);
    LOG_INFO("EXC ADDRESS  = 0x%x", cpu_dump[3]);
    */

    return true;
  } else {
    dif_rstmgr_reset_info_bitfield_t reset_info;
    reset_info = rstmgr_testutils_reason_get();
    LOG_ERROR("Unexpected reset_info 0x%x", reset_info);
  }
  return false;
}
