// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Values in `status_t` that are guaranteed to correspond to each
 * `otcrypto_status_t` value.
 *
 * If `OTCRYPTO_STATUS_DEBUG` is set, full line-number and module information
 * is included to ease debugging. Otherwise, we use the cryptolib error codes
 * directly.
 *
 * Note: These values bypass `status_create` to avoid having a function call in
 * error cases, where we may be under attack and complexity should be
 * minimized.
 */
#define OTCRYPTO_OK ((status_t){.value = kHardenedBoolTrue})

#define LAUNDERED_OTCRYPTO_OK \
  ((status_t){.value = (int)launder32(kHardenedBoolTrue)})

#ifdef OTCRYPTO_STATUS_DEBUG

#define OTCRYPTO_RECOV_ERR                                                  \
  ((status_t){.value = (int32_t)(0x80000000 |                               \
                                 status_encode_module_id(MODULE_ID) << 16 | \
                                 ((__LINE__ & 0x7ff) << 5) | kAborted)})
#define OTCRYPTO_FATAL_ERR                                             \
  ((status_t){.value =                                                 \
                  (int32_t)(0x80000000 |                               \
                            status_encode_module_id(MODULE_ID) << 16 | \
                            ((__LINE__ & 0x7ff) << 5) | kFailedPrecondition)})
#define OTCRYPTO_BAD_ARGS                                              \
  ((status_t){.value =                                                 \
                  (int32_t)(0x80000000 |                               \
                            status_encode_module_id(MODULE_ID) << 16 | \
                            ((__LINE__ & 0x7ff) << 5) | kInvalidArgument)})
#define OTCRYPTO_ASYNC_INCOMPLETE                                           \
  ((status_t){.value = (int32_t)(0x80000000 |                               \
                                 status_encode_module_id(MODULE_ID) << 16 | \
                                 ((__LINE__ & 0x7ff) << 5) | kUnavailable)})
#define OTCRYPTO_NOT_IMPLEMENTED                                            \
  ((status_t){.value = (int32_t)(0x80000000 |                               \
                                 status_encode_module_id(MODULE_ID) << 16 | \
                                 ((__LINE__ & 0x7ff) << 5) | kUnimplemented)})
#else

#define OTCRYPTO_RECOV_ERR \
  ((status_t){.value = kOtcryptoStatusValueInternalError})
#define OTCRYPTO_FATAL_ERR ((status_t){.value = kOtcryptoStatusValueFatalError})
#define OTCRYPTO_BAD_ARGS ((status_t){.value = kOtcryptoStatusValueBadArgs})
#define OTCRYPTO_ASYNC_INCOMPLETE \
  ((status_t){.value = kOtcryptoStatusValueAsyncIncomplete})
#define OTCRYPTO_NOT_IMPLEMENTED \
  ((status_t){.value = kOtcryptoStatusValueNotImplemented})

#endif

#if !defined(OT_DISABLE_HARDENING) && defined(OT_PLATFORM_RV32)
/**
 * Compiler optimization barrier for `HARDENED_TRY`.
 *
 * Placed in a `static OT_ALWAYS_INLINE` helper without `volatile` so LLVM
 * preserves identical source-location metadata and allows tail-merging of error
 * return blocks, while still preventing correlated-value propagation from
 * narrowing the `orig_ >= 0` sign check to `status_ == -1`.
 */
static OT_ALWAYS_INLINE uint32_t hardened_try_barrier_(uint32_t val) {
  asm("" : "+r"(val));
  return val;
}

/**
 * Hardened version of the `TRY` macro from `status.h`.
 *
 * Returns an error if `expr_` represents an error status (negative `int32_t`),
 * continues if `expr_` equals `OTCRYPTO_OK` (`kHardenedBoolTrue`), and traps on
 * any other value (including non-hardened `0` or corrupted positive values).
 *
 * To resist both single-instruction skips and wider instruction-fetch skips
 * (up to 8 bytes / two fetch words on Ibex) without bloating call sites, the
 * error and trap guards are split across an 8-byte distance:
 *   1. `addi rd, rd, -1` (2B compressed, in-place): maps all valid error codes
 *      (bit 31 set, non-zero lower bits) to negative values, `0` to `-1`,
 *      `INT32_MIN` (`0x80000000`) to `0x7fffffff` (traps fail-closed), and
 *      `kHardenedBoolTrue` (1849) to `1848`.
 *   2. `bltz rd, .L_err` (4B): branches to the tail-merged error epilogue,
 *      which restores `rd + 1`, traps if the restored value is non-negative
 *      (`bgez rd, .L_trap`, catching both `0` and any faulted branch from the
 *      OK path), and returns the original error status.
 *   3. `xori rd, rd, (kHardenedBoolTrue - 1)` (4B, in-place): maps `1848` to
 *      `0`, leaving any skipped error status (bit 31 set) non-zero.
 *   4. `bnez rd, .L_trap` (2B compressed): traps if non-zero. Because `bltz`
 *      and `xori` span 8 bytes, no 4B or 8B instruction-fetch skip can cover
 *      both `bltz` and `bnez`, so skipping the error branch always falls into
 *      the trap.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                                            \
  do {                                                                 \
    int32_t status_ = (expr_).value;                                   \
    asm volatile("addi %0, %0, -1" : "+r"(status_));                   \
    if (status_ < 0) {                                                 \
      int32_t orig_ =                                                  \
          (int32_t)(hardened_try_barrier_(OT_UNSIGNED(status_)) + 1u); \
      if (orig_ >= 0) {                                                \
        __builtin_trap();                                              \
      }                                                                \
      return (status_t){.value = orig_};                               \
    }                                                                  \
    asm volatile("xori %0, %0, %1"                                     \
                 : "+r"(status_)                                       \
                 : "i"(kHardenedBoolTrue - 1));                        \
    if (status_ != 0) {                                                \
      __builtin_trap();                                                \
    }                                                                  \
  } while (false)
// COVERAGE (FI CM) We do not cover the redundant checks of the HARDENED_TRY as
// they serve as redundant encoding against fault attacks.
#else  // !OT_PLATFORM_RV32 || OT_DISABLE_HARDENING
/**
 * Alternate version of HARDENED_TRY that is logically equivalent.
 *
 * This can be used to measure the code size and performance impact of
 * control-flow countermeasures.
 *
 * @param expr_ An expression that evaluates to a `status_t`.
 * @return The enclosed OK value.
 */
#define HARDENED_TRY(expr_)                                             \
  do {                                                                  \
    status_t status_ = expr_;                                           \
    if (status_.value != kHardenedBoolTrue) {                           \
      return (status_t){                                                \
          .value = (int32_t)(OT_UNSIGNED(status_.value) | 0x80000000)}; \
    }                                                                   \
  } while (false)

#endif  // OT_DISABLE_HARDENING

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_STATUS_H_
