// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simctrl.h"

#include <iostream>

SimCtrl::SimCtrl() : stop_requested_(false), success_(true) {}

void SimCtrl::RequestStop(bool success) {
  stop_requested_ = true;
  success_ &= success;
}

bool SimCtrl::StopRequested() { return stop_requested_; }

bool SimCtrl::TestPassed() { return success_; }

void SimCtrl::OnFinal() {
  std::cout << std::endl
            << "//-------------//" << std::endl
            << (success_ ? "// TEST PASSED //" : "// TEST FAILED //")
            << std::endl
            << "//-------------//" << std::endl;
}
