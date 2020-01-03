// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_FIXTURE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_FIXTURE_H_

#include <string>
#include <vector>

#include "sw/device/lib/dif/testing/mock_mmio.h"

namespace dif_test {
class DifTest {
 public:
  template <typename F>
  static bool NewTest(std::string name, F test) {
    DifTest new_test(name, test);
    AllTests()->push_back(new_test);
    return true;
  }

  static int RunAll();

 private:
  template <typename F>
  DifTest(std::string name, F test) : name_(name), test_(test) {}
  static std::vector<DifTest> *AllTests();

  std::string name_;
  MockDevice (*test_)();
};
}  // namespace dif_test

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_FIXTURE_H_
