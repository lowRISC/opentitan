// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%doc>
    This file is the "DIF library header template", which provides a base for
    manually-implmenting portions of a DIF for a new peripheral, defining all
    the declarations that would be expected of a DIF library as described in the
    README.md. This header includes the auto-generated DIF library header, whose
    template is defined in util/make_new_dif/dif_autogen.h.tpl.

    This file should be instantiated with the `util/make_new_dif.py` script.

    The script also includes additional options for controlling how the template
    is instantiated. After the script runs:
       - delete this comment, 
       - the #error below, and 
       - any unnecessary definitions.
    Finally, remember to run clang-format!

    Note, this template requires the following Python objects to be passed:

    1. ip: See util/make_new_dif.py for the definition of the `ip` obj.
</%doc>

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip.name_upper}_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip.name_upper}_H_

#error "This file is a template, and not real code."

/**
 * @file
 * @brief <a href="/book/hw/ip/${ip.name_snake}/">${ip.name_long_upper}</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_${ip.name_snake}_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Runtime configuration for ${ip.name_long_lower}.
 *
 * This struct describes (SOFTWARE) runtime information for one-time
 * configuration of the hardware.
 */
typedef struct dif_${ip.name_snake}_config {
  // Fields, if necessary.
} dif_${ip.name_snake}_config_t;


/**
 * Parameters for a ${ip.name_long_lower} transaction.
 */
typedef struct dif_${ip.name_snake}_transaction {
  // Your fields here.
} dif_${ip.name_snake}_transaction_t;

/**
 * An output location for a ${ip.name_long_lower} transaction.
 */
typedef struct dif_${ip.name_snake}_output {
  // Your fields here.
} dif_${ip.name_snake}_output_t;

/**
 * Configures ${ip.name_long_lower} with runtime information.
 *
 * This function should only need to be called once for the lifetime of
 * `handle`.
 *
 * @param ${ip.name_snake} A ${ip.name_long_lower} handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_configure(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_config_t config);

/**
 * Begins a ${ip.name_long_lower} transaction.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_${ip.name_snake}_end()`.
 *
 * @param ${ip.name_snake} A ${ip.name_long_lower} handle.
 * @param transaction Transaction configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_start(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_transaction_t transaction);

/** Ends a ${ip.name_long_lower} transaction, writing the results to the given output.
 *
 * @param ${ip.name_snake} A ${ip.name_long_lower} handle.
 * @param output Transaction output parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_end(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_output_t output);

/**
 * Locks out ${ip.name_long_lower} functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param ${ip.name_snake} A ${ip.name_long_lower} handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_lock(
  const dif_${ip.name_snake}_t *${ip.name_snake});

/**
 * Checks whether this ${ip.name_long_lower} is locked.
 *
 * @param ${ip.name_snake} A ${ip.name_long_lower} handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_is_locked(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip.name_upper}_H_
