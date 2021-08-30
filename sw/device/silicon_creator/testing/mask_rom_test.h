// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_TESTING_MASK_ROM_TEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_TESTING_MASK_ROM_TEST_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace mask_rom_test {

/**
 * Base class for mocks used in Mask ROM unit tests.
 *
 * If a class `Mock` derives from `GlobalMock<Mock>`, `GlobalMock<Mock>`
 * ensures that there is at most one instance of `Mock` at a time (checked at
 * runtime) and makes this instance globally accessible via the static `Mock
 * &Instance()` method.
 *
 * Mock classes should be globally accessible so that mock functions can call
 * their methods during tests. They can also be strict or nice depending on
 * tests' needs. Mock classes that satisfy both requirements can be defined as
 * follows:
 *
 *     namespace mask_rom_test {
 *     namespace internal {
 *     class MockFoo : public GlobalMock<MockFoo> {
 *       ...
 *     };
 *     }  // namespace internal
 *     // Type alias for making `internal::MockFoo` a strict mock.
 *     using MockFoo = testing::StrictMock<internal::MockFoo>;
 *     // Type alias for making `internal::MockFoo` a nice mock if needed.
 *     using NiceMockFoo = testing::NiceMock<internal::MockFoo>;
 *     ...
 *     }  // namespace mask_rom_test
 *
 * This construction also ensures that we cannot have `MockFoo` and
 * `NiceMockFoo` instantiated at the same time since they both derive from the
 * same class, i.e. `GlobalMock<internal::MockFoo>`.
 */
template <typename Mock>
class GlobalMock {
 public:
  GlobalMock() {
    if (instance_ != nullptr) {
      throw std::runtime_error("Mock is already instantiated.");
    }
    instance_ = static_cast<Mock *>(this);
  }

  // Note: Destructors of mock classes must be virtual for `testing::StrictMock`
  // and `testing::NiceMock` to work correctly.
  virtual ~GlobalMock() { instance_ = nullptr; }

  static Mock &Instance() {
    if (instance_ == nullptr) {
      throw std::runtime_error("Mock is not instantiated yet.");
    }
    return *instance_;
  }

  GlobalMock(const GlobalMock &) = delete;
  GlobalMock &operator=(const GlobalMock &) = delete;
  GlobalMock(GlobalMock &&) = delete;
  GlobalMock &operator=(GlobalMock &&) = delete;

 private:
  static Mock *instance_;
};
template <typename Mock>
Mock *GlobalMock<Mock>::instance_ = nullptr;

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
