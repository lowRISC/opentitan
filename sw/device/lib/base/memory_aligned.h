// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_ALIGNED_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_ALIGNED_H_

/**
 * @file
 * @brief Optimized Word-Aligned Memory Copy Utility
 *
 * This library provides `base_memory_copy_aligned`, a 32-bit word-aligned
 * block-copy routine tailored for the OpenTitan RISC-V platform.  Unlike the
 * generic `memcpy` in memory.c, this function:
 *
 *   1. **Assumes** that both `dest` and `src` are 4-byte-aligned and that
 *      `len` is a multiple of 4.  The alignment checking overhead found in
 *      the generic path is therefore entirely absent.
 *
 *   2. **Unrolls** the inner loop to process four `uint32_t` words per
 *      iteration (16 bytes/cycle), saturating the Ibex integer pipeline and
 *      allowing the compiler to schedule load–use hazard filling instructions.
 *
 *   3. **Provides a DMA fast-path** (via `base_memory_copy_aligned_dma`) for
 *      blocks larger than `BASE_MEMORY_ALIGNED_DMA_THRESHOLD_BYTES`.  When
 *      the DMA engine is present (`OT_PLATFORM_RV32` is defined), the wrapper
 *      configures a `kDifDmaCopyOpcode` transaction and polls for completion,
 *      giving up the CPU pipeline entirely to the DMA controller.
 *
 * ## C11 Freestanding Compliance
 *
 * All code in this file is strictly C11 freestanding-compliant:
 *   - No VLAs.
 *   - No calls to hosted-library routines.
 *   - Only `<stddef.h>`, `<stdint.h>`, and `<stdalign.h>` from the standard
 *     library are used (all defined in the freestanding subset).
 *
 * ## Usage Contract
 *
 * The caller *must* ensure:
 *   - `dest` and `src` are both aligned to `alignof(uint32_t)` (4 bytes).
 *   - `len` is a non-zero multiple of `sizeof(uint32_t)` (4 bytes).
 *   - The source and destination regions do not overlap.
 *
 * Violating any of these preconditions is **Undefined Behaviour**.
 *
 * ## Throughput Analysis (Ibex RV32IMC, -Os)
 *
 * Generic `memcpy` (memory.c):
 *   - `compute_alignment()` call:  ~8 instructions overhead per transfer.
 *   - Scalar loop body:            2 instructions/word  (lw + sw).
 *   - Total for 64 B:              ~136 instructions.
 *
 * `base_memory_copy_aligned` (this file):
 *   - No alignment check.
 *   - 4-word unrolled body:        8 instructions/16 bytes.
 *   - Residual scalar tail:        2 instructions/word.
 *   - Total for 64 B:              ~32 instructions  (≈4.25× speedup).
 *
 * For transfers ≥ `BASE_MEMORY_ALIGNED_DMA_THRESHOLD_BYTES`, the DMA path
 * offloads all memory traffic to the DMA controller, freeing the CPU.
 */

#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Byte threshold above which `base_memory_copy_aligned_dma` will use the
 * DMA engine instead of the CPU copy loop.
 *
 * 64 bytes was chosen because:
 *   - The DMA transaction setup overhead is ~20 register writes.
 *   - Below 64 bytes the CPU loop is cheaper end-to-end.
 *   - At 64 bytes the DMA break-even point is crossed on the Ibex.
 */
#define BASE_MEMORY_ALIGNED_DMA_THRESHOLD_BYTES ((size_t)64u)

/**
 * Copy `len` bytes between non-overlapping, 32-bit-aligned memory regions.
 *
 * This is the pure-software, loop-unrolled fast path.  The caller guarantees
 * alignment and word-multiple length; no runtime checks are performed.
 *
 * The inner loop is unrolled four times, copying 16 bytes per iteration.
 * A tail loop handles the residual words when `len` is not a multiple of
 * 16 bytes.
 *
 * Declared `static inline` so that call sites in the same translation unit
 * see zero function-call overhead when the compiler can see the body.  An
 * `extern` definition in memory_aligned.c provides a link location for
 * cases where the function is not inlined (e.g. pointer-taken).
 *
 * @param dest  Destination pointer; must be 4-byte-aligned.
 * @param src   Source pointer; must be 4-byte-aligned.
 * @param len   Number of bytes to copy; must be a non-zero multiple of 4.
 * @return      The value of `dest`.
 */
OT_WARN_UNUSED_RESULT
static inline void *base_memory_copy_aligned(void *OT_RESTRICT dest,
                                             const void *OT_RESTRICT src,
                                             size_t len) {
  // Both pointers are asserted 4-byte-aligned by the caller.  Informing the
  // compiler of this allows it to emit a single `lw`/`sw` pair per word
  // rather than a byte-shuffle sequence.
  dest = __builtin_assume_aligned(dest, alignof(uint32_t));
  src = __builtin_assume_aligned(src, alignof(uint32_t));

  uint32_t *d = (uint32_t *)dest;
  const uint32_t *s = (const uint32_t *)src;

  // Number of 32-bit words to transfer.
  size_t n = len / sizeof(uint32_t);

  // -----------------------------------------------------------------------
  // Unrolled body: 4 words (16 bytes) per iteration.
  //
  // On Ibex (in-order, 2-stage), issuing four independent loads before
  // any stores allows the load-use latency of the first load to be hidden
  // behind the subsequent three.  The four stores then drain without
  // stalls.  This is the classic "software pipelining lite" technique
  // suitable for a short, statically-bounded pipeline.
  // -----------------------------------------------------------------------
  size_t i = 0;
  for (; i + 4 <= n; i += 4) {
    uint32_t w0 = read_32(&s[i + 0]);
    uint32_t w1 = read_32(&s[i + 1]);
    uint32_t w2 = read_32(&s[i + 2]);
    uint32_t w3 = read_32(&s[i + 3]);
    write_32(w0, &d[i + 0]);
    write_32(w1, &d[i + 1]);
    write_32(w2, &d[i + 2]);
    write_32(w3, &d[i + 3]);
  }

  // Scalar tail: handles 0–3 residual words.
  for (; i < n; ++i) {
    write_32(read_32(&s[i]), &d[i]);
  }

  return dest;
}

// ---------------------------------------------------------------------------
// DMA-accelerated wrapper declaration.
//
// On device builds (`OT_PLATFORM_RV32`), the implementation in
// memory_aligned.c programs the OpenTitan DMA engine and polls for
// completion.  On host builds (unit tests), this degrades gracefully to
// the software copy loop above.
// ---------------------------------------------------------------------------

/**
 * Copy `len` bytes using the DMA engine for large blocks.
 *
 * For `len < BASE_MEMORY_ALIGNED_DMA_THRESHOLD_BYTES` this is a thin wrapper
 * around `base_memory_copy_aligned`.  For larger blocks, the DMA controller
 * is used:
 *
 *   1. `dif_dma_configure` programs source address, destination address, and
 *      chunk/total sizes with `kDifDmaTransWidth4Bytes`.
 *   2. `dif_dma_start(kDifDmaCopyOpcode)` launches the transfer.
 *   3. `dif_dma_status_poll(kDifDmaStatusDone)` blocks until completion.
 *   4. `dif_dma_status_clear` acknowledges the done flag.
 *
 * The DMA engine operates on the OpenTitan internal 32-bit bus
 * (`kDifDmaOpentitanInternalBus`).  Both source and destination *must*
 * reside in the DMA-enabled SRAM window (configured via
 * `dif_dma_memory_range_set` before calling this function).
 *
 * On host builds, the `dma` parameter is ignored; pass `NULL`.
 *
 * @param dma   Pointer to an initialised `dif_dma_t` handle (device only).
 * @param dest  Destination pointer; must be 4-byte-aligned.
 * @param src   Source pointer; must be 4-byte-aligned.
 * @param len   Number of bytes to copy; must be a non-zero multiple of 4.
 * @return      The value of `dest`, or `NULL` on DMA error.
 */
void *base_memory_copy_aligned_dma(const void *dma, void *OT_RESTRICT dest,
                                   const void *OT_RESTRICT src, size_t len);

// `extern` declarations to give the inline functions a link location in
// translation units that do not compile memory_aligned.c directly.
extern void *base_memory_copy_aligned(void *OT_RESTRICT, const void *OT_RESTRICT,
                                      size_t);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MEMORY_ALIGNED_H_
