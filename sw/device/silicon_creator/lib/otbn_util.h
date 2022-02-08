// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Constants related to OTBN wide words
 */
enum {
  /* Length of an OTBN wide word in bits */
  kOtbnWideWordNumBits = 256,
  /* Length of an OTBN wide word in words */
  kOtbnWideWordNumWords = kOtbnWideWordNumBits / (sizeof(uint32_t) * 8),
};

/**
 * Information about an embedded OTBN application image.
 *
 * All pointers reference data in the normal CPU address space.
 * uint32_t values are addresses in the OTBN address space.
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
   * Start of initialized OTBN data.
   *
   * Data in between dmem_data_start and dmem_data_end will be copied to OTBN
   * at app load time.
   */
  const uint32_t *dmem_data_start;
  /**
   * The first word after initialized OTBN data.
   *
   * Should satisfy `dmem_data_start <= dmem_data_end`.
   */
  const uint32_t *dmem_data_end;
} otbn_app_t;

/**
 * The address of an OTBN symbol as seen by OTBN
 *
 * Use `OTBN_DECLARE_SYMBOL_ADDR()` together with `OTBN_ADDR_T_INIT()` to
 * initialize this type.
 */
typedef uint32_t otbn_addr_t;

/**
 * OTBN context structure.
 *
 * Use `otbn_init()` to initialize.
 */
typedef struct otbn {
  /**
   * The application loaded or to be loaded into OTBN.
   *
   * Only valid if @p app_is_loaded is kHardenedBoolTrue.
   */
  otbn_app_t app;

  /**
   * Is the application loaded into OTBN?
   */
  hardened_bool_t app_is_loaded;

  /**
   * The error bits from the last execution of OTBN.
   */
  uint32_t error_bits;
} otbn_t;

/**
 * Generate the prefix to add to an OTBN symbol name used on the Ibex side
 *
 * The result is a pointer to Ibex's rodata that should be used to initialise
 * memory for that symbol.
 *
 * This is needed by the OTBN driver to support DMEM/IMEM ranges but
 * application code shouldn't need to use this. Use the `otbn_addr_t` type and
 * supporting macros instead.
 */
#define OTBN_SYMBOL_PTR(app_name, sym) _otbn_local_app_##app_name##_##sym

/**
 * Generate the prefix to add to an OTBN symbol name used on the OTBN side
 *
 * The result is a pointer whose integer value is the address by which the
 * symbol should be accessed in OTBN memory.
 *
 * This is an internal macro used in `OTBN_DECLARE_SYMBOL_ADDR` and
 * `OTBN_ADDR_T_INIT` but application code shouldn't need to use it directly.
 */
#define OTBN_SYMBOL_ADDR(app_name, sym) _otbn_remote_app_##app_name##_##sym

/**
 * Makes a symbol in the OTBN application image available.
 *
 * This is needed by the OTBN driver to support DMEM/IMEM ranges but
 * application code shouldn't need to use this. To get access to OTBN
 * addresses, use `OTBN_DECLARE_SYMBOL_ADDR` instead.
 */
#define OTBN_DECLARE_SYMBOL_PTR(app_name, symbol_name) \
  extern const uint32_t OTBN_SYMBOL_PTR(app_name, symbol_name)[]

/**
 * Makes the OTBN address of a symbol in the OTBN application available.
 *
 * Symbols are typically function or data pointers, i.e. labels in assembly
 * code. Unlike OTBN_DECLARE_SYMBOL_PTR, this will work for symbols in the .bss
 * section (which exist on the OTBN side, even though they don't have backing
 * data on Ibex).
 *
 * Use this macro instead of manually declaring the symbols as symbol names
 * might change.
 *
 * @param app_name    Name of the application the function is contained in.
 * @param symbol_name Name of the symbol (function, label).
 */
#define OTBN_DECLARE_SYMBOL_ADDR(app_name, symbol_name) \
  extern const uint32_t OTBN_SYMBOL_ADDR(app_name, symbol_name)[]

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
#define OTBN_DECLARE_APP_SYMBOLS(app_name)             \
  OTBN_DECLARE_SYMBOL_PTR(app_name, _imem_start);      \
  OTBN_DECLARE_SYMBOL_PTR(app_name, _imem_end);        \
  OTBN_DECLARE_SYMBOL_PTR(app_name, _dmem_data_start); \
  OTBN_DECLARE_SYMBOL_PTR(app_name, _dmem_data_end)

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
#define OTBN_APP_T_INIT(app_name)                                     \
  ((otbn_app_t){                                                      \
      .imem_start = OTBN_SYMBOL_PTR(app_name, _imem_start),           \
      .imem_end = OTBN_SYMBOL_PTR(app_name, _imem_end),               \
      .dmem_data_start = OTBN_SYMBOL_PTR(app_name, _dmem_data_start), \
      .dmem_data_end = OTBN_SYMBOL_PTR(app_name, _dmem_data_end),     \
  })

/**
 * Initializes an `otbn_addr_t`.
 */
#define OTBN_ADDR_T_INIT(app_name, symbol_name) \
  ((uint32_t)OTBN_SYMBOL_ADDR(app_name, symbol_name))

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
 * @param dest Address of the destination in OTBN's data memory.
 * @param src Source of the data to copy.
 * @return The result of the operation.
 */
rom_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len, const uint32_t *src,
                                   otbn_addr_t dest);

/**
 * Copies data from OTBN's data memory to CPU memory.
 *
 * @param ctx The context object.
 * @param len The number of 32b words to copy.
 * @param src The address in OTBN data memory to copy from.
 * @param[out] dest The destination of the copied data in main memory
 *                  (preallocated).
 * @return The result of the operation.
 */
rom_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len,
                                     const otbn_addr_t src, uint32_t *dest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_
