// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"
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
      .silicon_creator_id = 0,
      .product_id = 0,
      .revision_id = 0,
  };
}

uint32_t otp_read32(uint32_t address) { return kHardenedBoolTrue; }

dif_result_t dif_rstmgr_init(mmio_region_t base_addr, dif_rstmgr_t *rstmgr) {
  return kDifOk;
}

dif_result_t dif_rstmgr_reset_info_get(const dif_rstmgr_t *handle,
                                       dif_rstmgr_reset_info_bitfield_t *info) {
  *info = 1 << kRstmgrReasonPowerOn;
  return kDifOk;
}

dif_result_t dif_rstmgr_reset_info_clear(const dif_rstmgr_t *handle) {
  return kDifOk;
}

void rstmgr_reset(void) {
  while (true) {
  }
}
