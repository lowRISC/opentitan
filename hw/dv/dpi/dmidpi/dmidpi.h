// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef DMIDPI_H_
#define DMIDPI_H_

#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Constructor: Create and initialize dmidpi context object
 *
 * Call from a initial block.
 *
 * @param display_name Name of the interface (for display purposes only)
 * @param listen_port Port to listen on
 * @return an initialized struct dmidpi_ctx context object
 */
void *dmidpi_create(const char *display_name, int listen_port);

/**
 * Destructor: Close all connections and free all resources
 *
 * Call from a finish block.
 *
 * @param ctx_void  a struct dmidpi_ctx context object
 */
void dmidpi_close(void *ctx_void);

/**
 * Drive DMI signals
 *
 * Call this function from the simulation at every clock tick to read/write
 * from/to the DMI signals.
 *
 * @param ctx_void  a struct dmidpi_ctx context object
 */
void dmidpi_tick(void *ctx_void, svBit *dmi_req_valid,
                 const svBit dmi_req_ready, svBitVecVal *dmi_req_addr,
                 svBitVecVal *dmi_req_op, svBitVecVal *dmi_req_data,
                 const svBit dmi_resp_valid, svBit *dmi_resp_ready,
                 const svBitVecVal *dmi_resp_data,
                 const svBitVecVal *dmi_resp_resp, svBit *dmi_reset_n);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // DMIDPI_H_
