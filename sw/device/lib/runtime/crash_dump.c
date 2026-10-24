// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Implementation of the last-gasp crash-dump utility.
 *
 * ## Design Notes
 *
 * ### CSR Access Strategy
 *
 * OpenTitan uses the `CSR_READ(csr, &dest)` macro (defined in
 * `sw/device/lib/base/csr.h`) to read RISC-V Control and Status Registers.
 * On device builds (`OT_PLATFORM_RV32`) this expands to a single
 * `csrr %0, <imm>` instruction.  On host/unit-test builds it calls
 * `mock_csr_read(addr)`, which the test framework intercepts and controls.
 *
 * Using `CSR_READ` instead of raw `asm volatile("csrr ...")` gives us two
 * important properties:
 *   a) Identical host and device source paths — no `#ifdef OT_PLATFORM_RV32`
 *      guards scattered through the implementation.
 *   b) The mock framework can drive specific CSR values in unit tests without
 *      any specialised hardware.
 *
 * ### Retention SRAM Access
 *
 * The retention SRAM is a 4096-byte MMIO-like region that persists across
 * non-PoR resets.  Its base address is obtained through the device topology
 * layer:
 *
 *   retention_sram_get() → (retention_sram_t *)base_address
 *
 * The `crash_dump_t` record occupies the last 6 words (24 bytes) of the
 * 512-word owner reserved area.  This placement avoids interfering with
 * test harness code that uses the lower owner words for reset-sequencing
 * flags.
 *
 * Word index within `retention_sram_t::owner.reserved[]`:
 *   Words 0 .. 505   — available for other owner uses
 *   Words 506 .. 511 — crash_dump_t (6 × 4 = 24 bytes)
 *
 * The slot offset constant below is computed as:
 *   CRASH_DUMP_OWNER_WORD_OFFSET = 512 - (sizeof(crash_dump_t) / 4)
 *                                = 512 - 6 = 506
 *
 * ### Order of Writes
 *
 * The fields are written in this order:
 *   1. mepc, mcause, mtval, mstatus   (payload)
 *   2. reason                         (caller-supplied context)
 *   3. magic                          (sentinel — last, so an interrupted
 *                                      capture leaves magic == 0 and
 *                                      crash_dump_get() returns false)
 *
 * This ordering ensures that if the write sequence is interrupted (e.g., a
 * second watchdog bite fires before step 3), the partially-written record
 * will not be mistaken for a valid dump.
 *
 * ### Host Build Stub
 *
 * On non-RV32 host builds `retention_sram_get()` is unavailable (it calls
 * into the device topology layer).  The host-build alternative provides a
 * statically allocated `crash_dump_t` that the tests can inspect directly.
 * The public API (`crash_dump_capture`, `crash_dump_get`, `crash_dump_clear`)
 * is identical in both builds.
 */

#include "sw/device/lib/runtime/crash_dump.h"

#include <stdint.h>

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/csr_registers.h"
#include "sw/device/lib/base/macros.h"

// ---------------------------------------------------------------------------
// Word offset of the crash_dump_t within the owner reserved area.
// ---------------------------------------------------------------------------
// sizeof(crash_dump_t) == 24 bytes == 6 words.
// sizeof(retention_sram_owner_t::reserved) == 2048 bytes == 512 words.
// We place the record at the end: words 506..511.
#define CRASH_DUMP_OWNER_WORD_OFFSET \
  (512u - (uint32_t)(sizeof(crash_dump_t) / sizeof(uint32_t)))

// ---------------------------------------------------------------------------
// Backend: device build uses real retention SRAM; host build uses a local
// static buffer so that unit tests can link without the silicon_creator tree.
// ---------------------------------------------------------------------------

#ifdef OT_PLATFORM_RV32

#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

/**
 * Return a pointer to the `crash_dump_t` slot in retention SRAM.
 *
 * We cast through `uint32_t *` to avoid depending on the internal layout of
 * `retention_sram_owner_t`.  The slot always starts at word 506 of the owner
 * reserved[] array, which begins at offset 2048 within the retention_sram_t.
 */
static crash_dump_t *get_slot(void) {
  retention_sram_t *rsram = retention_sram_get();
  // Owner area starts at rsram->owner.reserved[0].
  // Slot begins at rsram->owner.reserved[CRASH_DUMP_OWNER_WORD_OFFSET].
  uint32_t *owner_base = rsram->owner.reserved;
  return (crash_dump_t *)(owner_base + CRASH_DUMP_OWNER_WORD_OFFSET);
}

#else  // !OT_PLATFORM_RV32

// Host / unit-test build: provide a static backing buffer.
// Tests can obtain a pointer to the stored record via crash_dump_get().
static crash_dump_t g_crash_dump_slot;

static crash_dump_t *get_slot(void) { return &g_crash_dump_slot; }

#endif  // OT_PLATFORM_RV32

// ---------------------------------------------------------------------------
// Public API implementation
// ---------------------------------------------------------------------------

void crash_dump_capture(crash_dump_reason_t reason) {
  // Step 1: Read the four CSRs.
  //
  // We read mepc first because it contains the faulting / interrupted PC,
  // which is the most time-critical value (in theory another NMI could fire
  // and corrupt mepc on a device with nested interrupts, though Ibex disables
  // MIE on trap entry so this is not a practical concern).
  uint32_t mepc;
  CSR_READ(CSR_REG_MEPC, &mepc);

  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);

  uint32_t mtval;
  CSR_READ(CSR_REG_MTVAL, &mtval);

  uint32_t mstatus;
  CSR_READ(CSR_REG_MSTATUS, &mstatus);

  // Step 2: Write payload, then reason, then magic (sentinel last).
  crash_dump_t *slot = get_slot();
  slot->mepc = mepc;
  slot->mcause = mcause;
  slot->mtval = mtval;
  slot->mstatus = mstatus;
  slot->reason = (uint32_t)reason;
  // Barrier: ensure all payload words are written before the magic sentinel.
  // On Ibex (in-order) this is guaranteed by the sequential write ordering,
  // but we add a compiler barrier to prevent the compiler from reordering
  // the magic write above the payload writes.
  __asm__ volatile("" ::: "memory");
  slot->magic = (uint32_t)kCrashDumpMagic;
}

bool crash_dump_get(crash_dump_t *out) {
  const crash_dump_t *slot = get_slot();
  if (slot->magic != (uint32_t)kCrashDumpMagic) {
    return false;
  }
  *out = *slot;
  return true;
}

void crash_dump_clear(void) {
  crash_dump_t *slot = get_slot();
  // Clear the magic sentinel first so that a concurrent (NMI-driven) call to
  // crash_dump_capture() cannot race with a partial clear.
  slot->magic = 0u;
  __asm__ volatile("" ::: "memory");
  slot->reason = 0u;
  slot->mepc = 0u;
  slot->mcause = 0u;
  slot->mtval = 0u;
  slot->mstatus = 0u;
}
