// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/testing/fixture.h"

#include <cstdio>
#include <vector>

namespace dif_test {
int DifTest::RunAll() {
  int exit_val = 0;
  for (auto &test : *AllTests()) {
    std::printf("Running %s...\n", test.name_.c_str());
    auto result = test.test_();
    if (result.failed_expectations == 0) {
      std::printf("Passed!\n");
      continue;
    }
    exit_val = 1;
    std::printf("Failed with %zu assertion failures\n",
                result.failed_expectations);
  }
  return exit_val;
}

std::vector<DifTest> *DifTest::AllTests() {
  static std::vector<DifTest> tests;
  return &tests;
}
}  // namespace dif_test
