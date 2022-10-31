// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_OTBN_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_OTBN_H_

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otbn.h"

/**
 * @file
 * @brief OpenTitan Big Number Accelerator (OTBN) driver
 */

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
  const uint8_t *imem_start;
  /**
   * End of OTBN instruction memory.
   */
  const uint8_t *imem_end;
  /**
   * Start of initialized OTBN data memory.
   *
   * Data in this section is copied into DMEM when the app is loaded.
   */
  const uint8_t *dmem_data_start;
  /**
   * End of initialized OTBN data memory.
   */
  const uint8_t *dmem_data_end;
} otbn_app_t;

/**
 * The address of an OTBN symbol as seen by OTBN
 *
 * Use `OTBN_DECLARE_SYMBOL_ADDR()` together with `OTBN_ADDR_T_INIT()` to
 * initialize this type.
 */
typedef uint32_t otbn_addr_t;

/**
 * The result of an OTBN operation.
 */
typedef enum otbn_result {
  /**
   * The operation succeeded.
   */
  kOtbnOk = 0,
  /**
   * An unspecified failure occurred.
   */
  kOtbnError = 1,
  /**
   * A precondition check for an argument passed into the function failed.
   */
  kOtbnBadArg = 2,
  /**
   * The operation performed on OTBN failed.
   *
   * More specific error information can be obtained with
   * `dif_otbn_get_err_code()`.
   */
  kOtbnOperationFailed = 3,
} otbn_result_t;

/**
 * OTBN context structure.
 *
 * Use `otbn_init()` to initialize.
 */
typedef struct otbn {
  /**
   * The OTBN DIF to access the hardware.
   */
  dif_otbn_t dif;

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
  extern const uint8_t OTBN_SYMBOL_PTR(app_name, symbol_name)[]

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
  extern const uint8_t OTBN_SYMBOL_ADDR(app_name, symbol_name)[]

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

/**
 * Initializes the OTBN context structure.
 *
 * @param ctx The context object.
 * @param base_addr The OTBN hardware base address.
 * @return The result of the operation.
 */
otbn_result_t otbn_init(otbn_t *ctx, mmio_region_t base_addr);

/**
 * (Re-)loads the application into OTBN.
 *
 * Load the application image with both instruction and data segments into OTBN.
 *
 * @param ctx The context object.
 * @param app The application to load into OTBN.
 * @return The result of the operation.
 */
otbn_result_t otbn_load_app(otbn_t *ctx, const otbn_app_t app);

/**
 * Starts the OTBN execute operation.
 *
 * Use `otbn_busy_wait_for_done()` to wait for execution to complete.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
otbn_result_t otbn_execute(otbn_t *ctx);

/**
 * Checks if OTBN is in busy status.
 *
 * @param ctx The context object
 * @param[out] is_busy Set to true if OTBN is not in idle or in an error state.
 * @return otbn_result_t The result of the operation.
 */
otbn_result_t otbn_busy_check(otbn_t *ctx, bool *is_busy);

/**
 * Busy waits for OTBN to be done with the current operation.
 *
 * After an operation, triggered by a command, OTBN is back in idle state.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
otbn_result_t otbn_busy_wait_for_done(otbn_t *ctx);

/**
 * Copies data from the CPU memory to OTBN data memory.
 *
 * @param ctx The context object.
 * @param len_bytes Number of bytes to copy.
 * @param dest Address of the destination in OTBN's data memory.
 * @param src Source of the data to copy.
 * @return The result of the operation.
 */
otbn_result_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len_bytes,
                                     const void *src, otbn_addr_t dest);

/**
 * Copies data from OTBN's data memory to CPU memory.
 *
 * @param ctx The context object.
 * @param len_bytes The number of bytes to copy.
 * @param src The address in OTBN data memory to copy from.
 * @param[out] dest The destination of the copied data in main memory
 *                  (preallocated).
 * @return The result of the operation.
 */
otbn_result_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len_bytes,
                                       otbn_addr_t src, void *dest);

/**
 * Overwrites all of OTBN's data memory with zeros.
 *
 * This function tries to perform the operation for all data words, even if
 * a single write fails.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
otbn_result_t otbn_zero_data_memory(otbn_t *ctx);

/**
 * Writes a LOG_INFO message with the contents of each 256b DMEM word.
 *
 * @param ctx The context object.
 * @param max_addr The highest address to dump. Set to 0 to output the whole
 *                 DMEM. Must be a multiple of WLEN.
 * @return The result of the operation.
 */
otbn_result_t otbn_dump_dmem(const otbn_t *ctx, uint32_t max_addr);

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_OTBN_H_
