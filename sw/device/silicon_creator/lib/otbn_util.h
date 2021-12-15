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
  /* Length of an OTBN wide word in bytes */
  kOtbnWideWordNumBytes = kOtbnWideWordNumBits / 8,
  /* Length of an OTBN wide word in words */
  kOtbnWideWordNumWords = kOtbnWideWordNumBytes / sizeof(uint32_t),
};

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
   * Pointer to the first byte of free DMEM space.
   *
   * Only valid if @p app_is_loaded is true.
   */
  otbn_ptr_t free_dmem;

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
otbn_error_t otbn_load_app(otbn_t *ctx, const otbn_app_t app);

/**
 * Start the OTBN application.
 *
 * Use `otbn_busy_wait_for_done()` to wait for the function call to complete.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
otbn_error_t otbn_execute_app(otbn_t *ctx);

/**
 * Busy waits for OTBN to be done with its operation.
 *
 * @param ctx The context object.
 * @return The result of the operation.
 */
otbn_error_t otbn_busy_wait_for_done(otbn_t *ctx);

/**
 * Copies data from the CPU memory to OTBN data memory.
 *
 * @param ctx The context object.
 * @param len Number of 32b words to copy.
 * @param dest Pointer to the destination in OTBN's data memory.
 * @param src Source of the data to copy.
 * @return The result of the operation.
 */
otbn_error_t otbn_copy_data_to_otbn(otbn_t *ctx, size_t len,
                                    const uint32_t *src, otbn_ptr_t dest);

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
otbn_error_t otbn_copy_data_from_otbn(otbn_t *ctx, size_t len,
                                      const otbn_ptr_t src, uint32_t *dest);

/**
 * Gets the address in OTBN data memory referenced by `ptr`.
 *
 * @param ctx The context object.
 * @param ptr The pointer to convert.
 * @return The address of the data in OTBN's data memory.
 */
uint32_t otbn_data_ptr_to_dmem_addr(const otbn_t *ctx, otbn_ptr_t ptr);

/**
 * Converts a DMEM address into a corresponding pointer in CPU memory.
 *
 * @param ctx The context object.
 * @param dmem_addr The address to convert.
 * @return The pointer in CPU memory.
 */
otbn_ptr_t otbn_dmem_addr_to_data_ptr(const otbn_t *ctx, uint32_t dmem_addr);

/**
 * Makes a single dptr symbol point to where its value is stored.
 *
 * After this routine, dmem[dptr] contains the DMEM address corresponding to
 * `value`.
 *
 * @param otbn The OTBN context
 * @param dptr Pointer to the dptr_* symbol
 * @param value Pointer to the value
 * @return The result of the operation.
 */
otbn_error_t set_data_pointer(otbn_t *otbn, const otbn_ptr_t dptr,
                              const otbn_ptr_t value);

/**
 * Sets a pointer to a certain amount of free space in DMEM.
 *
 * Aligns the destination pointer to the next free and 256-bit aligned DMEM
 * address and sets up the dptr to point to that address.
 *
 * Must be called when OTBN is idle. Errors on attempts to allocate past the
 * boundaries of DMEM.
 *
 * @param otbn The OTBN context
 * @param len The number of 32b words to allocate
 * @param dptr Pointer to the dptr_* symbol
 * @return The result of the operation.
 */
otbn_error_t otbn_dmem_alloc(otbn_t *otbn, size_t len, otbn_ptr_t dptr);

/**
 * Copies data from the CPU to OTBN DMEM.
 *
 * Writes data to the next free, 256-bit-aligned DMEM address. Then, sets up
 * the dptr to point to the newly written value, and internally updates the
 * OTBN context to indicate that those bytes are no longer free.
 *
 * Must be called when OTBN is idle. Errors on attempts to write past the
 * boundaries of DMEM.
 *
 * @param otbn The OTBN context
 * @param len The number of 32b words to copy
 * @param src Source of the data to copy
 * @param dptr Pointer to the dptr_* symbol
 * @return The result of the operation.
 */
otbn_error_t otbn_dmem_write_indirect(otbn_t *otbn, size_t len,
                                      const uint32_t *src, otbn_ptr_t dptr);

/**
 * Read the value pointed to by a DMEM pointer.
 *
 * Reads the address held in DMEM[dptr] and then copies `len` words from DMEM
 * to CPU main memory starting at that address.
 *
 * Errors if the read is outside DMEM, or if the address read from the dptr is
 * not 32b-aligned.
 *
 * @param otbn The OTBN context
 * @param len The number of 32b words to copy
 * @param dptr Pointer to the dptr_* symbol
 * @param dest Pointer to the destination in CPU memory
 * @return The result of the operation.
 */
otbn_error_t otbn_dmem_read_indirect(otbn_t *otbn, size_t len, otbn_ptr_t dptr,
                                     uint32_t *dest);

/**
 * Evaluate an expression and return a mask ROM error if the result is an
 * OTBN error.
 *
 * @param expr_ An expression which results in an otbn_error_t.
 */
#define FOLD_OTBN_ERROR(expr_)          \
  do {                                  \
    otbn_error_t local_error_ = expr_;  \
    if (local_error_ != kOtbnErrorOk) { \
      return kErrorOtbnInternal;        \
    }                                   \
  } while (0)

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_UTIL_H_
