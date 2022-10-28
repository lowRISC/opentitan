// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_SHARED_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_SHARED_H_

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_csrng.h"

/**
 * Private code shared between the CSRNG and EDN DIFs.
 */

enum {
  /**
   * CSRNG genbits buffer size in uint32_t words.
   */
  kCsrngGenBitsBufferSize = 4,
};

/**
 * Supported CSRNG application commands.
 * See https://docs.opentitan.org/hw/ip/csrng/doc/#command-header for
 * details.
 */
typedef enum csrng_app_cmd_id {
  kCsrngAppCmdInstantiate = 1,
  kCsrngAppCmdReseed = 2,
  kCsrngAppCmdGenerate = 3,
  kCsrngAppCmdUpdate = 4,
  kCsrngAppCmdUnisntantiate = 5,
} csrng_app_cmd_id_t;

/**
 * CSRNG application interface command header parameters.
 */
typedef struct csrng_app_cmd {
  /**
   * Application command.
   */
  csrng_app_cmd_id_t id;
  /**
   * Entropy source enable.
   *
   * Mapped to flag0 in the hardware command interface.
   */
  dif_csrng_entropy_src_toggle_t entropy_src_enable;
  /**
   * Seed material. Only used in `kCsrngAppCmdInstantiate`, `kCsrngAppCmdReseed`
   * and `kCsrngAppCmdUpdate` commands.
   */
  const dif_csrng_seed_material_t *seed_material;
  /**
   * Generate length. Specified as number of 128bit blocks.
   */
  uint32_t generate_len;
} csrng_app_cmd_t;

/**
 * Builds a CSRNG command header.
 *
 * Build a CSRNG command header following the CSRNG specification. The caller is
 * responsible for verifying the correctness of the parameters passed into this
 * function.
 *
 * @param id CSRNG command ID.
 * @param entropy_src_enable Entropy source enable flag. Mapped to flag0 in the
 * command header.
 * @param cmd_len The overall command lend. It should be set to the number of
 * seed material words, or zero.
 * @param generate_len Number of 128bit blocks to request if the command ID is
 * set to `kCsrngAppCmdGenerate`.
 * @return CSRNG command header in `uint32_t` format.
 */
OT_WARN_UNUSED_RESULT
uint32_t csrng_cmd_header_build(
    csrng_app_cmd_id_t id, dif_csrng_entropy_src_toggle_t entropy_src_enable,
    uint32_t cmd_len, uint32_t generate_len);

/**
 * Writes application command `cmd` to the CSRNG_CMD_REQ_REG register.
 * Returns the result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t csrng_send_app_cmd(mmio_region_t base_addr, ptrdiff_t offset,
                                csrng_app_cmd_t cmd);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_SHARED_H_
