// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"

// TODO(#12905): This file includes fake definitions for the functions that are
// used by the silicon_creator bootstrap implementation and to set reset_reason
// but missing in the english breakfast top level due to hardware limitations.

#if !OT_IS_ENGLISH_BREAKFAST
#error "This file should be compiled only for the english breakfast top level"
#endif

void lifecycle_hw_rev_get(lifecycle_hw_rev_t *hw_rev) {
  *hw_rev = (lifecycle_hw_rev_t){
      .chip_gen = 0,
      .chip_rev = 0,
  };
}

uint32_t otp_read32(uint32_t address) { return kHardenedBoolTrue; }

uint32_t rstmgr_reason_get(void) { return 1 << kRstmgrReasonPowerOn; }

void rstmgr_reason_clear(uint32_t reasons) {}

void rstmgr_reset(void) {
  while (true) {
  }
}
