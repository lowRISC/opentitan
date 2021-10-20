// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_aes_autogen.h"

#include "aes_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_init(mmio_region_t base_addr, dif_aes_t *aes) {
  if (aes == NULL) {
    return kDifBadArg;
  }

  aes->base_addr = base_addr;

  return kDifOk;
}
