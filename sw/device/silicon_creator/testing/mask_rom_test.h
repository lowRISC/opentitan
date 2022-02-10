// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_TESTING_MASK_ROM_TEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_TESTING_MASK_ROM_TEST_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace mask_rom_test {

/**
 * Test fixture for mask ROM tests.
 *
 * Test suites should derive their test fixtures from this class. This class
 * enforces that mock methods are called in the order `EXPECT_CALL` statements
 * are written. In cases where this behavior is not desired, test fixtures can
 * derive from `Unordered<MaskRomTest>` instead to opt-out.
 */
class MaskRomTest : public testing::Test {
 protected:
  std::unique_ptr<testing::InSequence> seq_ =
      std::make_unique<testing::InSequence>();
};

/**
 * Mixin for unordered calls.
 *
 * @see MaskRomTest.
 */
template <typename T>
class Unordered : public T {
 protected:
  Unordered() : T() { T::seq_.reset(); }
};

}  // namespace mask_rom_test
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_TESTING_MASK_ROM_TEST_H_
