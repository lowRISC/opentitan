// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "env/debug_environment.h"

#include <iostream>

DebugEnvironment::DebugEnvironment()
    : simctrl_(new SimCtrl()), dv_test_(new DVTest()) {}

DebugEnvironment::~DebugEnvironment() {
  delete dv_test_;
  delete simctrl_;
}

void DebugEnvironment::OnInitial(unsigned int seed, char *test) {
  std::cout << "Env initialized" << std::endl
            << "Test: " << test << ", seed: " << seed << std::endl;
  if (!dv_test_->ReadTestConfig(test)) {
    simctrl_->RequestStop(false);
  } else {
    dv_test_->PrintConfig();
  }
}

void DebugEnvironment::OnFinal() { simctrl_->PrintSimResult(); }

void DebugEnvironment::GetStopReq(unsigned char *stop_req) {
  *stop_req = simctrl_->StopRequested();
}
