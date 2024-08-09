// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_PRIM_DV_PRIM_ASCON_ASCON_MODEL_DPI_ASCON_MODEL_DPI_H_
#define OPENTITAN_HW_IP_PRIM_DV_PRIM_ASCON_ASCON_MODEL_DPI_ASCON_MODEL_DPI_H_

#include "svdpi.h"
#include "vendor/ascon_ascon-c/ascon128/ascon.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Perform one ascon round.
 *
 * @param  data_i  Input data is expected to be 320 bit ascon state size
 * @param  round_i Round Number
 * @param  data_o  Output data
 */
void c_dpi_ascon_round(const svBitVecVal *data_i, svBit *round_i,
                       svBitVecVal *data_o);

/**
 * Get packed data block from simulation.
 *
 * @param  data_i Input data from simulation
 * @return Pointer to data copied to memory, 0 in case of an error
 */
ascon_state_t *ascon_data_get(const svBitVecVal *data_i);

/**
 * Write packed data block to simulation and free the source buffer afterwards.
 *
 * @param  data_o Output data for simulation
 * @param  data   Data to be copied to simulation, freed after the operation
 */
void ascon_data_put(svBitVecVal *data_o, ascon_state_t *data);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // OPENTITAN_HW_IP_PRIM_DV_PRIM_ASCON_ASCON_MODEL_DPI_ASCON_MODEL_DPI_H_
