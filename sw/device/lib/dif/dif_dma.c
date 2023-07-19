// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_dma.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"

#include "dma_regs.h"  // Generated.

static_assert(kDifDmaOpentitanInternalBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_OT_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCControlRegisterBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SOC_ADDR,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaSoCSystemBus ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_SYS_ADDR_,
              "Address Space ID mismatches with value defined in HW");
static_assert(kDifDmaOpentitanExternalFlash ==
                  DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_VALUE_FLASH_ADDR,
              "Address Space ID mismatches with value defined in HW");

dif_result_t dif_dma_configure(const dif_dma_t *dma,
                               dif_dma_transaction_t transaction) {
  return kDifUnavailable;
}

dif_result_t dif_dma_handshake_enable(const dif_dma_t *dma,
                                      dif_dma_handshake_t handshake) {
  return kDifUnavailable;
}
dif_result_t dif_dma_start(const dif_dma_t *dma,
                           dif_dma_transaction_opcode_t opcode) {
  return kDifUnavailable;
}

dif_result_t dif_dma_abort(const dif_dma_t *dma) { return kDifUnavailable; }

dif_result_t dif_dma_lock(const dif_dma_t *dma) { return kDifUnavailable; }

dif_result_t dif_dma_is_locked(const dif_dma_t *dma, bool *is_locked) {
  return kDifUnavailable;
}
