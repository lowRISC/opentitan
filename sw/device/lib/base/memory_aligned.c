// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Implementation of the optimized word-aligned memory copy utility.
 *
 * This file provides:
 *   1. The link-time definition of `base_memory_copy_aligned` (the inline
 *      function declared in memory_aligned.h).
 *   2. `base_memory_copy_aligned_dma`, the hardware-accelerated wrapper that
 *      delegates to the OpenTitan DMA engine for transfers above the threshold.
 *
 * ## Design Decisions
 *
 * ### Why `static inline` in the header?
 *
 * `base_memory_copy_aligned` is declared `static inline` so that each call
 * site in device firmware that includes the header gets a private, inlined
 * copy of the function body.  This eliminates the call/return overhead (two
 * instructions on Ibex: `jal ra, target` + `jalr zero, 0(ra)`) and enables
 * the compiler to propagate constant `len` values, further unrolling the
 * loop at compile time.
 *
 * The `extern` definition in this file provides a unique link-time address so
 * that the function can be pointed to (e.g., from a function pointer table)
 * without violating the ODR equivalent in C11.
 *
 * ### DMA threshold
 *
 * Setting up a DMA transaction costs approximately:
 *   - 2 × mmio_region_write32  (src address lo/hi)
 *   - 2 × mmio_region_write32  (dst address lo/hi)
 *   - 2 × mmio_region_write32  (src/dst config)
 *   - 1 × mmio_region_write32  (ASID)
 *   - 2 × mmio_region_write32  (chunk/total size)
 *   - 1 × mmio_region_write32  (transfer width)
 *   - 1 × mmio_region_write32  (GO bit)
 *   Total: ~11 MMIO writes ≈ 110 CPU cycles at 1 cycle/write.
 *
 * The CPU loop for 64 bytes (16 words, 4-unrolled) is ~32 instructions ≈
 * 32–48 cycles.  The crossover where DMA wins is therefore at or slightly
 * above 64 bytes, which matches our chosen threshold.
 */

#include "sw/device/lib/base/memory_aligned.h"

#include <stddef.h>
#include <stdint.h>

// Provide the link-time definition of the inline function declared in the
// header.  This single extern definition satisfies C11 §6.7.4p7 and avoids
// "multiple definition" linker errors when the header is included by more than
// one translation unit in a non-inlining build (e.g., -O0 debug builds).
extern void *base_memory_copy_aligned(void *restrict dest,
                                      const void *restrict src, size_t len);

// ---------------------------------------------------------------------------
// DMA-backed implementation
// ---------------------------------------------------------------------------

#ifdef OT_PLATFORM_RV32

// Device build: use the real DMA engine.
#include "sw/device/lib/dif/dif_dma.h"

void *base_memory_copy_aligned_dma(const void *dma_handle,
                                   void *restrict dest,
                                   const void *restrict src, size_t len) {
  // Fast path: below the DMA threshold use the CPU loop.
  if (len < BASE_MEMORY_ALIGNED_DMA_THRESHOLD_BYTES) {
    return base_memory_copy_aligned(dest, src, len);
  }

  const dif_dma_t *dma = (const dif_dma_t *)dma_handle;

  // Build the transaction descriptor.
  //
  // Both source and destination live on the OpenTitan 32-bit internal bus.
  // We use the maximum transfer width (4 bytes) to allow the DMA controller
  // to issue word-wide bus transactions, matching the SRAM bus width and
  // avoiding read-modify-write cycles.
  dif_dma_transaction_t txn = {
      .source =
          {
              .address = (uint64_t)(uintptr_t)src,
              .asid = kDifDmaOpentitanInternalBus,
          },
      .destination =
          {
              .address = (uint64_t)(uintptr_t)dest,
              .asid = kDifDmaOpentitanInternalBus,
          },
      .src_config =
          {
              .wrap = false,
              .increment = true,
          },
      .dst_config =
          {
              .wrap = false,
              .increment = true,
          },
      .chunk_size = len,
      .total_size = len,
      .width = kDifDmaTransWidth4Bytes,
  };

  // Program the DMA controller.
  if (dif_dma_configure(dma, txn) != kDifOk) {
    return NULL;
  }

  // Launch the transfer.
  if (dif_dma_start(dma, kDifDmaCopyOpcode) != kDifOk) {
    return NULL;
  }

  // Spin-wait for completion.  On device firmware this is acceptable because:
  //   a) SRAM-to-SRAM copies are latency-bound, not compute-bound.
  //   b) We do not yet have an RTOS context that could yield.
  //
  // An interrupt-driven variant could be added in a future PR.
  if (dif_dma_status_poll(dma, kDifDmaStatusDone) != kDifOk) {
    // A bus error or other fault was detected.
    (void)dif_dma_abort(dma);
    (void)dif_dma_status_clear(dma);
    return NULL;
  }

  // Acknowledge the done flag so the DMA controller is ready for the next
  // transaction.
  (void)dif_dma_status_clear(dma);

  return dest;
}

#else  // !OT_PLATFORM_RV32

// Host / unit-test build: the DMA engine is not present.  Degrade gracefully
// to the software copy so that tests can exercise `base_memory_copy_aligned`
// through the DMA wrapper without requiring a mock DMA.
void *base_memory_copy_aligned_dma(const void *dma_handle,
                                   void *restrict dest,
                                   const void *restrict src, size_t len) {
  (void)dma_handle;
  return base_memory_copy_aligned(dest, src, len);
}

#endif  // OT_PLATFORM_RV32
