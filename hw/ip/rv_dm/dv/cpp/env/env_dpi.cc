// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Environment DPI calls

#include "debug_environment.h"
#include "svdpi.h"

#ifdef __cplusplus
extern "C" {
#endif

DebugEnvironment *env;

/**
 * Initial call creates and sets up the C++ environment
 *
 * @param seed Simulation seed is passed from SV to C++
 * @param test Name of test to load
 */
void env_initial(unsigned int *seed, char *test) {
  env = new DebugEnvironment();
  env->OnInitial(*seed, test);
}

/**
 * Tick checks each cycle whether simulation stop has been requested
 *
 * @param stop_req Pass a stop request from C++ to SV
 */
void env_tick(svBit *stop_req) { env->GetStopReq(stop_req); }

/**
 * Clean up C++ environment when SV ends simulation
 */
void env_final() {
  env->OnFinal();
  delete env;
}

#ifdef __cplusplus
}
#endif
