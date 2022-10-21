// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_BASE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_BASE_H_

/**
 * @file
 * @brief Shared macros and headers for DIFs.
 */

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/multibits.h"

#define USING_INTERNAL_STATUS
#include "sw/device/lib/base/internal/status.h"
#undef USING_INTERNAL_STATUS

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Evaluate an expression and return if the result is an error.
 *
 * @param expr_ An expression which results in an dif_result_t.
 */
#define DIF_RETURN_IF_ERROR(expr_)       \
  do {                                   \
    dif_result_t local_error_ = (expr_); \
    if (local_error_ != kDifOk) {        \
      return local_error_;               \
    }                                    \
  } while (false)

/**
 * The result of a DIF operation.
 *
 * NOTE: additional result values can be defined in the manually-implemented
 * header by creating an additional *_result_t enum type. See the Lifecycle
 * Controller DIF for how this may be implemented.
 */
typedef enum dif_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifOk = kOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifError = kInternal,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifBadArg = kInvalidArgument,
  /**
   * The operation failed because writes to a required register are
   * disabled.
   */
  kDifLocked = kFailedPrecondition,
  /**
   * The operation failed because the IP is processing an operation, and will
   * finish in some amount of time. A function that returns this error may be
   * retried at any time, and is guaranteed to have not produced any side
   * effects.
   */
  kDifUnavailable = kUnavailable,
  /**
   * Indicates that the Ip's FIFO (if it has one or more of) is full.
   */
  kDifIpFifoFull = kResourceExhausted,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that would go out of range.
   */
  kDifOutOfRange = kOutOfRange,
  /**
   * Indicates that the attempted operation would attempt a read/write to an
   * address that is not aligned.
   */
  kDifUnaligned = kUnimplemented,
} dif_result_t;

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_toggle {
  /**
   * The "disabled" state.
   */
  kDifToggleDisabled = 0,
  /**
   * The "enabled" state.
   */
  kDifToggleEnabled = 1,
} dif_toggle_t;

/**
 * An interrupt type: event, or status.
 *
 * This enum may be used instead when describing an interrupt type.
 * Specifically, event interrupts require software to manually clear them by
 * writing to the interrupt status register (after handling the root cause),
 * while status interrupts clear immediately when the root cause of the iterrupt
 * has been handled.
 */
typedef enum dif_irq_type {
  /**
   * Event type interrupt.
   */
  kDifIrqTypeEvent = 0,
  /**
   * Status type interrupt.
   */
  kDifIrqTypeStatus = 1,
} dif_irq_type_t;

/**
 * Checks if a DIF toggle type is valid.
 *
 * @param val A potential dif_toggle_t value.
 * @return Bool indicating validity of toggle value.
 */
inline bool dif_is_valid_toggle(dif_toggle_t val) {
  switch (val) {
    case kDifToggleEnabled:
      return true;
    case kDifToggleDisabled:
      return true;
    default:
      return false;
  }
}

/**
 * Converts a `dif_toggle_t` to a `bool`.
 *
 * @param val A dif_toggle_t value.
 * @return Corresponding bool value.
 */
inline bool dif_toggle_to_bool(dif_toggle_t val) {
  switch (val) {
    case kDifToggleEnabled:
      return true;
    case kDifToggleDisabled:
      return false;
    default:
      return false;
  }
}

/**
 * Converts a bool to a `dif_toggle_t`.
 *
 * @param val A bool value.
 * @return Corresponding dif_toggle_t value.
 */
inline dif_toggle_t dif_bool_to_toggle(bool val) {
  return val ? kDifToggleEnabled : kDifToggleDisabled;
}

/**
 * Converts a multi-bit bool to a `dif_toggle_t`.
 *
 * @param val A multi-bit bool value.
 * @return Corresponding dif_toggle_t value.
 */
inline dif_toggle_t dif_multi_bit_bool_to_toggle(multi_bit_bool_t val) {
  switch (val) {
    case kMultiBitBool4True:
    case kMultiBitBool8True:
    case kMultiBitBool12True:
    case kMultiBitBool16True:
      return kDifToggleEnabled;
    default:
      return kDifToggleDisabled;
  }
}

/**
 * Converts a `dif_toggle_t` to a `multi_bit_bool_t` of 4 bits.
 *
 * @param val A `dif_toggle_t` value.
 * @return Corresponding `multi_bit_bool_t` value. Invalid values resolve to
 * "false".
 */
inline multi_bit_bool_t dif_toggle_to_multi_bit_bool4(dif_toggle_t val) {
  if (val == kDifToggleEnabled) {
    return kMultiBitBool4True;
  } else {
    return kMultiBitBool4False;
  }
}

/**
 * Converts a `dif_toggle_t` to a `multi_bit_bool_t` of 8 bits.
 *
 * @param val A `dif_toggle_t` value.
 * @return Corresponding `multi_bit_bool_t` value. Invalid values resolve to
 * "false".
 */
inline multi_bit_bool_t dif_toggle_to_multi_bit_bool8(dif_toggle_t val) {
  if (val == kDifToggleEnabled) {
    return kMultiBitBool8True;
  } else {
    return kMultiBitBool8False;
  }
}

/**
 * Converts a `dif_toggle_t` to a `multi_bit_bool_t` of 12 bits.
 *
 * @param val A `dif_toggle_t` value.
 * @return Corresponding `multi_bit_bool_t` value. Invalid values resolve to
 * "false".
 */
inline multi_bit_bool_t dif_toggle_to_multi_bit_bool12(dif_toggle_t val) {
  if (val == kDifToggleEnabled) {
    return kMultiBitBool12True;
  } else {
    return kMultiBitBool12False;
  }
}

/**
 * Converts a `dif_toggle_t` to a `multi_bit_bool_t` of 16 bits.
 *
 * @param val A `dif_toggle_t` value.
 * @return Corresponding `multi_bit_bool_t` value. Invalid values resolve to
 * "false".
 */
inline multi_bit_bool_t dif_toggle_to_multi_bit_bool16(dif_toggle_t val) {
  if (val == kDifToggleEnabled) {
    return kMultiBitBool16True;
  } else {
    return kMultiBitBool16False;
  }
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_BASE_H_
