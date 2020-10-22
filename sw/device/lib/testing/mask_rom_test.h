// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_MASK_ROM_TEST_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_MASK_ROM_TEST_H_

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace mask_rom_test {

/**
 * Mixin for global mocks.
 *
 * `GlobalMock<T>` is a derived class of `T` that can have at most one instance
 * at a time (checked at runtime) and makes this instance globally accessible
 * via the static `GlobalMock<T> &Instance()` method.
 *
 * Mock classes used in tests should be of this type so that mock functions can
 * access their instances during tests. Since we prefer using strict mocks,
 * mock classes should also be of type `testing::StrictMock`. Mock classes that
 * satisfy both requirements can be defined using a type alias as follows:
 *
 *     namespace mask_rom_test {
 *     namespace internal {
 *     class MockFoo {
 *       ...
 *     };
 *     }  // namespace internal
 *     // Type alias for making `internal::MockFoo` a global and strict mock.
 *     using MockFoo = GlobalMock<testing::StrictMock<internal::MockFoo>>;
 *     ...
 *     }  // namespace mask_rom_test
 */
template <typename T>
class GlobalMock : public T {
 public:
  template <typename... Args>
  GlobalMock(Args &&... args) : T(std::forward(args)...) {
    if (instance_ != nullptr) {
      throw std::runtime_error("Mock is already instantiated.");
    }
    instance_ = this;
  }

  static_assert(std::has_virtual_destructor<T>::value,
                "Mock class must have a virtual destructor.");
  virtual ~GlobalMock() { instance_ = nullptr; }

  static GlobalMock<T> &Instance() {
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
  static GlobalMock<T> *instance_;
};
template <typename T>
GlobalMock<T> *GlobalMock<T>::instance_ = nullptr;

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
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_MASK_ROM_TEST_H_
