// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

#include "sw/device/lib/dif/autogen/dif_pinmux_autogen.h"

#include "pinmux_regs.h"  // Generated.

OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_init(mmio_region_t base_addr, dif_pinmux_t *pinmux) {
  if (pinmux == NULL) {
    return kDifBadArg;
  }

  pinmux->base_addr = base_addr;

  return kDifOk;
}
