// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ascon_model_dpi.h"

#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "svdpi.h"
#include "vendor/ascon_ascon-c/ascon128/round.h"

void c_dpi_ascon_round(const svBitVecVal *data_i, svBit *round_i,
                       svBitVecVal *data_o) {
  uint8_t round;

  // get input data from simulator
  ascon_state_t *state = ascon_data_get(data_i);
  round = (uint8_t)*round_i;

  ROUND(state, round);

  ascon_data_put(data_o, state);

  return;
}

ascon_state_t *ascon_data_get(const svBitVecVal *data_i) {
  ascon_state_t *data;

  // alloc data buffer
  data = (ascon_state_t *)malloc(sizeof(ascon_state_t));
  assert(data);

  // get data from simulator, convert from 2D to 1D
  printf("Getter:\n");
  for (int i = 0; i < 5; i++) {
    svBitVecVal value;

    value = data_i[2 * i];
    data->x[i] = (uint64_t)value;
    printf("Value of data_i = %X\n", value);
    value = data_i[(2 * i) + 1];
    data->x[i] |= ((uint64_t)value) << 32;
    printf("Value of data_i = %X\n", value);
    printf("Value of   X[%i] = %jX\n", i, data->x[i]);
  }

  return data;
}

void ascon_data_put(svBitVecVal *data_o, ascon_state_t *data) {
  printf("Putter:\n");
  // convert from 1D to 2D, write output data to simulation
  for (int i = 0; i < 5; i++) {
    svBitVecVal value;

    printf("Value of   X[%i] = %jX\n", i, data->x[i]);
    value = (svBitVecVal)(data->x[i]);
    printf("Value of data_o = %X\n", value);
    data_o[(2 * i)] = value;
    value = (svBitVecVal)((data->x[i]) >> (32));
    printf("Value of data_o = %X\n", value);
    data_o[(2 * i) + 1] = value;
  }

  // free data
  free(data);

  return;
}
