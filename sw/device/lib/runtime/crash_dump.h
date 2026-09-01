// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_CRASH_DUMP_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_CRASH_DUMP_H_

/**
 * @file
 * @brief Last-Gasp Post-Mortem Crash-Dump Utility
 *
 * ## Purpose
 *
 * In a field-deployed Root of Trust, two classes of fatal events can occur
 * without leaving any trace that survives a device reset:
 *
 *   1. **Watchdog bite** — the AON-timer watchdog fires because firmware
 *      stopped petting it.  The hardware issues a full chip reset via the
 *      reset manager.
 *
 *   2. **Unhandled exception** — the default machine-mode trap handler is
 *      invoked for an exception that the application has no recovery path
 *      for (e.g., instruction access fault, load access fault, illegal
 *      instruction).  On OpenTitan this normally calls `abort()` which
 *      triggers a watchdog bite or a software-requested reset.
 *
 * In both cases, the RISC-V CSRs that record the fault information —
 * `mepc` (faulting PC), `mcause` (exception/interrupt code), `mtval`
 * (trap-specific address or instruction word), `mstatus` (privilege and
 * interrupt-enable flags) — are **cleared on reset** and therefore lost.
 *
 * This utility captures those CSRs and a caller-supplied reason code into
 * a fixed-layout structure in the **Retention SRAM**, which is the only
 * memory guaranteed to persist across a non-Power-on-Reset event (watchdog
 * bite, software reset).  After the reset, a boot-time diagnostic routine
 * can examine the structure to reconstruct exactly where and why the
 * previous firmware instance died.
 *
 * ## Retention SRAM Layout
 *
 * The retention SRAM is 4 KiB with the layout defined in
 * `sw/device/silicon_creator/lib/drivers/retention_sram.h`:
 *
 *   Offset  0x000  – 0x003   version (uint32_t)
 *   Offset  0x004  – 0x7FF   creator area (2044 B, managed by ROM/ROM_EXT)
 *   Offset  0x800  – 0xFFF   owner area (2048 B, 512 × uint32_t, reserved[])
 *
 * The **owner reserved area** is cleared only on Power-on-Reset (PoR).
 * It is not modified by the silicon creator boot stages during a watchdog-
 * or software-triggered reset.  This makes it the correct location for the
 * crash dump.
 *
 * We place `crash_dump_t` at the **end** of the owner reserved area
 * (highest addresses).  This avoids colliding with other in-tree uses of
 * the owner area that grow upward from offset 0x800.
 *
 * Layout within owner reserved[] (2048 B = 512 words):
 *   [0 .. 506]  available for other owner-area uses
 *   [507]       crash_dump_t.magic        (4 B)
 *   [508]       crash_dump_t.reason       (4 B)
 *   [509]       crash_dump_t.mepc         (4 B)
 *   [510]       crash_dump_t.mcause       (4 B)
 *   [511]       crash_dump_t.mtval        (4 B)
 *   [512] = end of owner area (4096 B from base)
 *
 * Note: `mstatus` (32 bits) is packed together with `reason` so the total
 * footprint is exactly 5 words (20 bytes).
 *
 * ## Integration
 *
 * ### Watchdog-bite NMI handler (dif_aon_timer):
 *
 * ```c
 * void ottf_nmi_handler(void) {
 *   crash_dump_capture(kCrashDumpReasonWatchdog);
 *   // Let the watchdog bite issue a reset (or explicitly call shutdown).
 * }
 * ```
 *
 * ### Default machine-mode exception handler:
 *
 * ```c
 * void ottf_exception_handler(void) {
 *   crash_dump_capture(kCrashDumpReasonException);
 *   abort();
 * }
 * ```
 *
 * ### Boot-time diagnostic read-back:
 *
 * ```c
 * crash_dump_t dump;
 * if (crash_dump_get(&dump)) {
 *   LOG_INFO("Last crash: reason=%d mepc=0x%08x mcause=0x%08x",
 *            dump.reason, dump.mepc, dump.mcause);
 * }
 * ```
 *
 * ## C11 Freestanding Compliance
 *
 * This header includes only `<stdint.h>` and `<stdbool.h>`, both of which are
 * in the freestanding subset.  No VLAs, no hosted-library calls.
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// ---------------------------------------------------------------------------
// Magic sentinel
// ---------------------------------------------------------------------------

/**
 * Magic value written into `crash_dump_t.magic` by `crash_dump_capture()`.
 *
 * On cold power-on the retention SRAM is scrambled by ROM; the probability
 * of the sentinel value being present spuriously is ~2^{-32}.  Boot code
 * should check this field before trusting the remaining fields.
 *
 * Value chosen to be unique and human-readable in a hex dump: "CRDP".
 */
enum { kCrashDumpMagic = 0x43524450u };

// ---------------------------------------------------------------------------
// Crash reason codes
// ---------------------------------------------------------------------------

/**
 * Enumeration of crash capture triggers.
 *
 * These reason codes are stored verbatim in `crash_dump_t.reason` so that
 * boot-time diagnostics can distinguish the source of the dump without
 * inspecting `mcause`.
 */
typedef enum crash_dump_reason {
  /**
   * No crash has been recorded since the last Power-on-Reset.
   * Callers should not read other fields when this value is seen.
   */
  kCrashDumpReasonNone = 0,

  /**
   * The dump was captured by the watchdog-bite NMI handler.
   *
   * In this case `mepc` is the PC of the instruction that was interrupted
   * when the NMI arrived, and `mcause` encodes the NMI cause (bit 31 set,
   * cause = 0x1f on Ibex for the watchdog NMI).
   */
  kCrashDumpReasonWatchdog = 1,

  /**
   * The dump was captured by the default machine-mode exception handler.
   *
   * In this case `mepc` is the faulting instruction's PC, `mcause` encodes
   * the exception code (bit 31 clear), and `mtval` holds exception-specific
   * auxiliary information (faulting address or instruction word).
   */
  kCrashDumpReasonException = 2,

  /**
   * The dump was captured from a manually invoked call site (e.g., a
   * CHECK() failure handler or an explicit `crash_dump_capture` call from
   * application code).
   */
  kCrashDumpReasonManual = 3,
} crash_dump_reason_t;

// ---------------------------------------------------------------------------
// Crash dump record
// ---------------------------------------------------------------------------

/**
 * Post-mortem crash dump record.
 *
 * This struct is stored directly in the retention SRAM owner area and must
 * therefore:
 *   - Be exactly word-aligned (all fields are uint32_t).
 *   - Have no padding inserted by the compiler (all members are the same
 *     width, so the compiler will not insert padding).
 *
 * The `magic` field must be checked before trusting any other field.
 */
typedef struct crash_dump {
  /**
   * Sentinel value.  Valid iff equal to `kCrashDumpMagic`.
   */
  uint32_t magic;

  /**
   * Reason code identifying the capture trigger.
   *
   * Stored as a uint32_t to keep the struct uniformly word-sized.
   * Cast to `crash_dump_reason_t` before use.
   */
  uint32_t reason;

  /**
   * Value of the `mepc` CSR at capture time.
   *
   * For exceptions: the PC of the faulting instruction.
   * For NMIs (watchdog bark): the PC of the interrupted instruction.
   */
  uint32_t mepc;

  /**
   * Value of the `mcause` CSR at capture time.
   *
   * Bit 31 set: interrupt.  Bits 30:0: cause code.
   * Bit 31 clear: exception.  Bits 30:0: exception code.
   *
   * Ibex-specific cause codes are enumerated in `ibex_exc_t` (ibex.h).
   */
  uint32_t mcause;

  /**
   * Value of the `mtval` CSR at capture time.
   *
   * For load/store faults: the faulting address.
   * For misaligned accesses: the address of the missing transaction part.
   * For illegal instruction faults: the instruction word.
   * For all other exceptions: 0.
   */
  uint32_t mtval;

  /**
   * Value of the `mstatus` CSR at capture time.
   *
   * Records the machine interrupt-enable (MIE), machine previous privilege
   * (MPP), machine previous interrupt-enable (MPIE), and other flags that
   * describe the processor state at the moment of the fault.
   */
  uint32_t mstatus;
} crash_dump_t;

// Compile-time layout assertions: every field must be a word offset.
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, magic, 0);
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, reason, 4);
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, mepc, 8);
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, mcause, 12);
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, mtval, 16);
OT_ASSERT_MEMBER_OFFSET(crash_dump_t, mstatus, 20);
OT_ASSERT_SIZE(crash_dump_t, 24);

// ---------------------------------------------------------------------------
// API
// ---------------------------------------------------------------------------

/**
 * Capture the current CPU state into the retention SRAM crash-dump record.
 *
 * This function reads `mepc`, `mcause`, `mtval`, and `mstatus` from the
 * RISC-V CSRs, writes them — along with the supplied `reason` code and the
 * magic sentinel — into the fixed `crash_dump_t` slot at the end of the
 * retention SRAM owner area, and returns.
 *
 * It is designed to be called from:
 *   - The watchdog-bite NMI handler.
 *   - The default machine-mode exception handler.
 *   - Any CHECK()-failure or abort() path that precedes a reset.
 *
 * **This function does NOT reset the device.**  The caller is responsible
 * for initiating the reset (or letting the watchdog bite do so).
 *
 * **Re-entrancy:** this function is NOT re-entrant.  It must be called at
 * most once per fault event.  Calling it twice for the same reset event
 * will overwrite the first record.
 *
 * @param reason  The trigger that caused this capture.
 */
void crash_dump_capture(crash_dump_reason_t reason);

/**
 * Read the most recent crash-dump record from retention SRAM.
 *
 * If the magic sentinel is valid, the record is copied into `*out` and the
 * function returns `true`.  Otherwise (no crash has been recorded since
 * the last Power-on-Reset, or the retention SRAM has been scrambled),
 * `*out` is left unmodified and the function returns `false`.
 *
 * @param[out] out  Destination for the dump record.
 * @return          `true` iff a valid record was found.
 */
OT_WARN_UNUSED_RESULT
bool crash_dump_get(crash_dump_t *out);

/**
 * Erase the crash-dump record in retention SRAM.
 *
 * Clears the magic sentinel, invalidating the record.  Subsequent calls
 * to `crash_dump_get` will return `false` until the next call to
 * `crash_dump_capture`.
 *
 * Typically called after the boot-time diagnostic routine has logged the
 * record, so that a subsequent watchdog-bite reset does not re-display a
 * stale record.
 */
void crash_dump_clear(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_CRASH_DUMP_H_
