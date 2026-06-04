// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_nvm_ctrl.h"

// All calls here forward to dif_flash_ctrl.  When moving to a different NVM
// technology, replace the bodies of these functions with the new DIF calls.

dif_result_t dif_nvm_ctrl_init_state(dif_nvm_ctrl_state_t *nvm,
                                     mmio_region_t base_addr) {
  return dif_flash_ctrl_init_state(nvm, base_addr);
}
