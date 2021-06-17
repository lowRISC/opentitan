// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include <assert.h>

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

volatile retention_sram_t *retention_sram_get(void) {
  static_assert(sizeof(retention_sram_t) == TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES,
                "Unexpected retention SRAM size.");
  return (volatile retention_sram_t *)TOP_EARLGREY_RAM_RET_AON_BASE_ADDR;
}

void retention_sram_clear(void) {
  *retention_sram_get() = (retention_sram_t){0};
}
