// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_environment.h"

#include "svdpi.h"

#include <map>
#include <string>

#ifdef __cplusplus
extern "C" {
#endif

RegisterEnvironment *reg_env;

void env_initial(svBitVecVal *seed) {
  // Create TB environment
  reg_env = new RegisterEnvironment();

  // Initial setup
  reg_env->OnInitial(*seed);
}

void env_final() {
  reg_env->OnFinal();
  delete reg_env;
}

void env_tick(svBit *stop_req) { reg_env->GetStopReq(stop_req); }

#ifdef __cplusplus
}
#endif
