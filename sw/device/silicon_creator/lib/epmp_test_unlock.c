// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/epmp_test_unlock.h"

#include <assert.h>
#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"

bool epmp_unlock_test_status(void) {
  // PMP entry dedicated to test status (DV).
  enum {
    kEntry = 6,
  };

  // Permissions to apply to test status address space.
  const epmp_perm_t kPerm = kEpmpPermLockedReadWrite;

  // Check that address space is word aligned.
  if (kDeviceTestStatusAddress % sizeof(uint32_t) != 0) {
    return false;
  }

  // Update the shadow register values.
  epmp_region_t region = {.start = kDeviceTestStatusAddress,
                          .end = kDeviceTestStatusAddress + sizeof(uint32_t)};
  epmp_state_configure_na4(kEntry, region, kPerm);

  // Update the hardware registers.
  static_assert(kEntry == 6, "PMP entry has changed, update CSR operations.");
  CSR_WRITE(CSR_REG_PMPADDR6, kDeviceTestStatusAddress / sizeof(uint32_t));
  CSR_SET_BITS(CSR_REG_PMPCFG1, (kEpmpModeNa4 | kPerm)
                                    << ((kEntry % sizeof(uint32_t)) * 8));

  // Double check that the shadow registers match.
  if (!epmp_state_check()) {
    return false;
  }

  return true;
}
