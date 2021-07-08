// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Information about an embedded OTBN application image.
 *
 * All pointers reference data in the normal CPU address space.
 *
 * Use `OTBN_DECLARE_APP_SYMBOLS()` together with `OTBN_APP_T_INIT()` to
 * initialize this structure.
 */
typedef struct otbn_app {
  /**
   * Start of OTBN instruction memory.
   */
  const uint32_t *imem_start;
  /**
   * The first word after OTBN instruction memory.
   *
   * This address satifies `imem_len = imem_end - imem_start`.
   */
  const uint32_t *imem_end;
  /**
   * Start of OTBN data memory.
   */
  const uint32_t *dmem_start;
  /**
   * The first word after OTBN data memory.
   *
   * This address satifies `dmem_len = dmem_end - dmem_start`.
   */
  const uint32_t *dmem_end;
} otbn_app_t;

/**
 * A pointer to a symbol in OTBN's instruction or data memory.
 *
 * Use `OTBN_DECLARE_PTR_SYMBOL()` together with `OTBN_PTR_T_INIT()` to
 * initialize this type.
 *
 * The value of the pointer is an address in the normal CPU address space, and
 * must be first converted into OTBN address space before it can be used there.
 */
typedef uint32_t *otbn_ptr_t;

/**
 * OTBN context structure.
 *
 * Use `otbn_init()` to initialize.
 */
typedef struct otbn {
  /**
   * The application loaded or to be loaded into OTBN.
   *
   * Only valid if @p app_is_loaded is true.
   */
  otbn_app_t app;

  /**
   * Is the application loaded into OTBN?
   */
  bool app_is_loaded;

  /**
   * The error bits from the last execution of OTBN.
   */
  uint32_t error_bits;
} otbn_t;

/**
 * Makes an embedded OTBN application image available for use.
 *
 * Make symbols available that indicate the start and the end of instruction
 * and data memory regions, as they are stored in the device memory.
 *
 * Use this macro instead of manually declaring the symbols as symbol names
 * might change.
 *
 * @param app_name Name of the application to load, which is typically the
 *                 name of the main (assembly) source file.
 */
#define OTBN_DECLARE_APP_SYMBOLS(app_name)                    \
  extern const uint32_t _otbn_app_##app_name##__imem_start[]; \
  extern const uint32_t _otbn_app_##app_name##__imem_end[];   \
  extern const uint32_t _otbn_app_##app_name##__dmem_start[]; \
  extern const uint32_t _otbn_app_##app_name##__dmem_end[]

/**
 * Initializes the OTBN application information structure.
 *
 * After making all required symbols from the application image available
 * through `OTBN_DECLARE_APP_SYMBOLS()`, use this macro to initialize an
 * `otbn_app_t` struct with those symbols.
 *
 * @param app_name Name of the application to load.
 * @see OTBN_DECLARE_APP_SYMBOLS()
 */
#define OTBN_APP_T_INIT(app_name)                       \
  ((otbn_app_t){                                        \
      .imem_start = _otbn_app_##app_name##__imem_start, \
      .imem_end = _otbn_app_##app_name##__imem_end,     \
      .dmem_start = _otbn_app_##app_name##__dmem_start, \
      .dmem_end = _otbn_app_##app_name##__dmem_end,     \
  })

/**
 * Makes a symbol in the OTBN application image available.
 *
 * Symbols are typically function or data pointers, i.e. labels in assembly
 * code.
 *
 * Use this macro instead of manually declaring the symbols as symbol names
 * might change.
 *
 * @param app_name    Name of the application the function is contained in.
 * @param symbol_name Name of the symbol (function, label).
 */
#define OTBN_DECLARE_PTR_SYMBOL(app_name, symbol_name) \
  extern const uint32_t _otbn_app_##app_name##_##symbol_name[]

/**
 * Initializes an `otbn_ptr_t`.
 */
#define OTBN_PTR_T_INIT(app_name, symbol_name) \
  ((otbn_ptr_t)_otbn_app_##app_name##_##symbol_name)

void otbn_init(otbn_t *ctx);

/**
 * (Re-)loads the RSA application into OTBN.
 *
 * Load the application image with both instruction and data segments into OTBN.
 *
 * @param ctx The context object.
 * @param app The application to load into OTBN.
 * @return The result of the operation.
 */
rom_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app);

/**
 * Start the OTBN application.
 *
 * Use `otbn_busy_wait_for_done()` to wait for the function call to complete.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
rom_error_t otbn_execute_app(otbn_t *ctx);

/**
 * Busy waits for OTBN to be done with its operation.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
rom_error_t otbn_busy_wait_for_done(otbn_t *ctx);

/**
 * Copies data from the CPU memory to OTBN data memory.
 *
 * @param ctx The context object.
 * @param len Number of 32b words to copy.
 * @param dest Pointer to the destination in OTBN's data memory.
 * @param src Source of the data to copy.
 * @return The result of the operation.
 */
rom_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len, const uint32_t *src,
                                   otbn_ptr_t dest);

/**
 * Copies data from OTBN's data memory to CPU memory.
 *
 * @param ctx The context object.
 * @param len The number of 32b words to copy.
 * @param src The pointer in OTBN data memory to copy from.
 * @param[out] dest The destination of the copied data in main memory
 *                  (preallocated).
 * @return The result of the operation.
 */
rom_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len,
                                     const otbn_ptr_t src, uint32_t *dest);

/**
 * Gets the address in OTBN data memory referenced by `ptr`.
 *
 * @param ctx The context object.
 * @param ptr The pointer to convert.
 * @param[out] dmem_addr_otbn The address of the data in OTBN's data memory.
 * @return The result of the operation; #kOtbnBadArg if `ptr` is not in the data
 *         memory space of the currently loaded application.
 */
rom_error_t otbn_data_ptr_to_dmem_addr(const otbn_t *ctx, otbn_ptr_t ptr,
                                       uint32_t *dmem_addr_otbn);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_
