// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef JTAGDPI_H_
#define JTAGDPI_H_

#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

struct jtagdpi_ctx;

/**
 * Constructor: Create and initialize jtagdpi context object
 *
 * Call from a initial block.
 *
 * @param display_name Name of the JTAG interface (for display purposes only)
 * @param listen_port Port to listen on
 * @return an initialized struct jtagdpi_ctx context object
 */
void *jtagdpi_create(const char *display_name, int listen_port);

/**
 * Destructor: Close all connections and free all resources
 *
 * Call from a finish block.
 *
 * @param ctx_void  a struct jtagdpi_ctx context object
 */
void jtagdpi_close(void *ctx_void);

/**
 * Drive JTAG signals
 *
 * Call this function from the simulation at every clock tick to read/write
 * from/to the JTAG signals.
 *
 * @param ctx_void  a struct jtagdpi_ctx context object
 * @param tck       JTAG test clock signal
 * @param tms       JTAG test mode select signal
 * @param tdi       JTAG test data input signal
 * @param trst_n    JTAG test reset signal (active low)
 * @param srst_n    JTAG system reset signal (active low)
 * @param tdo       JTAG test data out
 */
void jtagdpi_tick(void *ctx_void, svBit *tck, svBit *tms, svBit *tdi,
                  svBit *trst_n, svBit *srst_n, const svBit tdo);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // JTAGDPI_H_
