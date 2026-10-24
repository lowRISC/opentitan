// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gtest/gtest.h"
#include "sw/device/lib/coverage/smoke/target.h"

namespace coverage_smoke_unittest {

TEST(CoverageTest, RunCovfuncCovered) { covfunc_hit(); }

TEST(CoverageTest, RunInlineCovfuncCovered) { inline_covfunc_hit(); }

TEST(CoverageTest, RunStaticInlineCovfuncCovered) {
  static_inline_covfunc_hit();
}

}  // namespace coverage_smoke_unittest
