// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_environment.h"

RegisterEnvironment::RegisterEnvironment(CSRParams params)
    : params_(params),
      simctrl_(new SimCtrl()),
      reg_model_(new RegisterModel(simctrl_, &params_)),
      reg_driver_(new RegisterDriver("reg_driver", reg_model_, simctrl_)),
      rst_driver_(new ResetDriver("rstn_driver")) {}

void RegisterEnvironment::OnInitial(unsigned int seed) {
  rst_driver_->OnInitial(seed);
  reg_driver_->OnInitial(seed);
}

void RegisterEnvironment::OnFinal() {
  reg_driver_->OnFinal();
  rst_driver_->OnFinal();
  simctrl_->OnFinal();
  delete rst_driver_;
  delete reg_driver_;
  delete reg_model_;
  delete simctrl_;
}

void RegisterEnvironment::GetStopReq(unsigned char *stop_req) {
  *stop_req = simctrl_->StopRequested();
}

void RegisterEnvironment::GetTestPass(unsigned char *test_passed) {
  *test_passed = simctrl_->TestPassed();
}
