// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CFI_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CFI_H_

#include "sw/device/lib/base/hardened.h"

/**
 * @brief Control Flow Integrity (CFI).
 *
 * The CFI_FUNC_COUNTER macros provide utilities to implement forward-edge and
 * block level control flow checks in software. The checks are based on
 * per-function counters that are monotonically incremented when the current
 * value matches the provided static expected value.
 *
 * To integrate CFI_FUNC_COUNTER checks into a module, first define a table
 * enumerating all the functions that need to be included in control flow
 * checks along with counter initial values, for example:
 *
 * ```
 * #define CFI_FUNC_COUNTERS_TABLE(X) \
 *  X(kCfiFunc1, 0x705) \
 *  X(kCfiFunc2, 0x042) \
 *  X(kCfiFunc3, 0x29d) \
 * ```
 *
 * It is recommended to use 11-bit initial values to enable the use of load
 * immediate instructions in the generated assembly.
 *
 * Use the `CFI_DEFINE_COUNTERS()` macro to initialize the counter table as well
 * as constant values required by the CFI framework. The following example uses
 * the table definition from the previous step.
 *
 * ```
 * CFI_DEFINE_COUNTERS(counters_table, CFI_FUNC_COUNTERS_TABLE);
 * ```
 *
 * Forward-edge checks:
 *
 * In the following example, func1 initializes the fnc2 counter before calling
 * the function using the `CFI_FUNC_COUNTER_PREPCALL()` macro. Both function
 * counters are checked after fnc2 returns, which gives a high level of
 * confidence that the control flow executed as expected.
 *
 * ```
 * void func2(void) {
 *  CFI_FUNC_COUNTER_INCREMENT(counters_table, kCfiFunc2, 1);
 *  ...
 *  CFI_FUNC_COUNTER_INCREMENT(counters_table, kCfiFunc2, 2);
 *  ...
 *  CFI_FUNC_COUNTER_INCREMENT(counters_table, kCfiFunc2, 3);
 * }
 *
 * void func1(void) {
 *  CFI_FUNC_COUNTER_INIT(counters_table, kCfiFunc1);
 *
 *  CFI_FUNC_COUNTER_PREPCALL(counters_table, kCfiFunc1, 1, kCfiFunc2);
 *  func2();
 *  CFI_FUNC_COUNTER_INCREMENT(counters_table, kCfiFunc1, 3);
 *  CFI_FUNC_COUNTER_CHECK(counters_table, kCfiFunc2, 4);
 * }
 * ```
 *
 * The implementation is based on https://hal.inria.fr/hal-01059201, with the
 * exception that all counters are expected to have good hamming distance
 * initialization and increment values to defend against potential faults. This
 * delta comes at a low cost given that all comparisons are performed against
 * constant values.
 */

/**
 * Defines all counter initialization constants. Used inside
 * `CFI_DEFINE_COUNTERS()`.
 */
#define CFI_FUNC_COUNTER_INIT_CONSTANTS_(name_, value_) name_##Val0 = value_,

/**
 * Initializes all counter values to zero. Used inside `CFI_DEFINE_COUNTERS()`.
 */
#define CFI_FUNC_COUNTERS_TABLE_INIT_(name_, value_) 0,

/**
 * Defines counter indexes. Used inside `CFI_DEFINE_COUNTERS()`.
 */
#define CFI_FUNC_COUNTER_INDEXES_(name_, value_) name_,

/**
 * Defines the counters table as well as constants required by other CFI counter
 * macros.
 *
 * @param table_name_ Name of the array variable used to store all the counters.
 * @param table_ Macro enumerating all the function identifiers and their
 * respective initial values.
 */
#define CFI_DEFINE_COUNTERS(table_name_, table_)     \
  enum { table_(CFI_FUNC_COUNTER_INIT_CONSTANTS_) }; \
  enum { table_(CFI_FUNC_COUNTER_INDEXES_) };        \
  uint32_t table_name_[] = {table_(CFI_FUNC_COUNTERS_TABLE_INIT_)}

enum {
  // Counter increment constant used in counter initialization and increment
  // operations.
  kCfiIncrement = 0x5a,
};

/**
 * Initializes the CFI counter at `index` with its respective initialization
 * constant plus `kCfiIncrement`.
 *
 * This macro calls `barrier32()` to synchronize the counter update.
 *
 * @param table The counters array variable.
 * @param index The counter index.
 */
#define CFI_FUNC_COUNTER_INIT(table, index)       \
  do {                                            \
    table[index] = (index##Val0 + kCfiIncrement); \
    barrier32(table[index]);                      \
  } while (0)

/**
 * Converts a CFI step value into an expected counter value.
 *
 * @param index The counter index.
 * @param step The increment step.
 */
#define CFI_STEP_TO_COUNT(index, step) ((index##Val0) + (step)*kCfiIncrement)

/**
 * Increments the CFI counter at `index` if the current count is equivalent to
 * the provided `step`. It throws an irrecoverable exception otherwise.
 *
 * This macro calls `barrier32()` to synchronize the counter update.
 *
 * @param table The counters array variable.
 * @param index The counter index.
 * @param step The equivalent step for the current counter value.
 */
#define CFI_FUNC_COUNTER_INCREMENT(table, index, step)               \
  do {                                                               \
    HARDENED_CHECK_EQ(table[index], CFI_STEP_TO_COUNT(index, step)); \
    table[index] += kCfiIncrement;                                   \
    barrier32(table[index]);                                         \
  } while (0)

/**
 * Prepare counters for function call.
 *
 * The `src` and `target` counters are associated with the caller and the
 * callee functions, respectively. The caller uses this macro to initialize
 * the `target` counter between increments of the `src` counter.
 *
 * The `src` counter can be verified at a later time to get a high confidence
 * measurement that the target counter was initialized properly by the caller
 * before entering the callee function.
 *
 * This macro uses `CFI_FUNC_COUNTER_INCREMENT()` and  `CFI_FUNC_COUNTER_INIT()`
 * which use `barrier32()` to synchronize all counter updates. An irrecoverable
 * exception is thrown if an unexpected `src` count value is found.
 *
 * @param table The counters array variable.
 * @param src Index counter associated with the caller function.
 * @param src_step Initial expected step of the `src` counter.
 * @param target Index counter associated with the calee function.
 */
#define CFI_FUNC_COUNTER_PREPCALL(table, src, src_step, target) \
  do {                                                          \
    CFI_FUNC_COUNTER_INCREMENT(table, src, src_step);           \
    CFI_FUNC_COUNTER_INIT(table, target);                       \
    CFI_FUNC_COUNTER_INCREMENT(table, src, (src_step + 1));     \
  } while (0)

/**
 * Compares the equivalent counter value of the counter at `index` against the
 * provided `step` value. Throws an irrecoverable exception on mismatch.
 *
 * @param table The counters array variable.
 * @param index The counter index.
 * @param step The equivalent step for the counter value.
 */
#define CFI_FUNC_COUNTER_CHECK(table, index, step)                   \
  do {                                                               \
    HARDENED_CHECK_EQ(table[index], CFI_STEP_TO_COUNT(index, step)); \
  } while (0)

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CFI_H_
