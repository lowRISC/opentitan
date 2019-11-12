// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simctrl.h"

#include <iostream>

SimCtrl::SimCtrl() : stop_request_(false), test_success_(true) {}

void SimCtrl::RequestStop(bool success) {
  stop_request_ = true;
  test_success_ &= success;
}

bool SimCtrl::StopRequested() { return stop_request_; }

bool SimCtrl::TestPass() { return test_success_; }

void SimCtrl::PrintSimResult() {
  std::cout << std::endl << "/////////////////" << std::endl;
  if (test_success_) {
    std::cout << "// TEST PASSED //";
  } else {
    std::cout << "// TEST FAILED //";
  }
  std::cout << std::endl << "/////////////////" << std::endl << std::endl;
}
