// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_environment.h"
#include "register_types.h"

#include "svdpi.h"

#include <map>
#include <string>

#ifdef __cplusplus
extern "C" {
#endif

RegisterEnvironment *reg_env;

void env_initial(svBitVecVal *seed, svBit PMPEnable,
                 svBitVecVal *PMPGranularity, svBitVecVal *PMPNumRegions,
                 svBitVecVal *MHPMCounterNum, svBitVecVal *MHPMCounterWidth) {
  // Package up parameters
  CSRParams params;
  params.PMPEnable = PMPEnable;
  params.PMPGranularity = *PMPGranularity;
  params.PMPNumRegions = *PMPNumRegions;
  params.MHPMCounterNum = *MHPMCounterNum;
  params.MHPMCounterWidth = *MHPMCounterWidth;
  // Create TB environment
  reg_env = new RegisterEnvironment(params);

  // Initial setup
  reg_env->OnInitial(*seed);
}

void env_final() {
  reg_env->OnFinal();
  delete reg_env;
}

void env_tick(svBit *stop_req, svBit *test_passed) {
  reg_env->GetStopReq(stop_req);
  reg_env->GetTestPass(test_passed);
}

#ifdef __cplusplus
}
#endif
