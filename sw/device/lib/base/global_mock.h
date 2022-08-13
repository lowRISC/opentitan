// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_GLOBAL_MOCK_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_GLOBAL_MOCK_H_

#include <sstream>
#include <typeinfo>
#include <utility>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace global_mock {

/**
 * Base class for mocks used in unit tests.
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
 *     namespace global_mock {
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
 *     }  // namespace rom_test
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
      std::stringstream ss;
      ss << "Mock `" << typeid(GlobalMock).name()
         << "` is already instantiated.";
      throw std::runtime_error(std::move(ss).str());
    }
    instance_ = static_cast<Mock *>(this);
  }

  // Note: Destructors of mock classes must be virtual for `testing::StrictMock`
  // and `testing::NiceMock` to work correctly.
  virtual ~GlobalMock() { instance_ = nullptr; }

  static Mock &Instance() {
    if (instance_ == nullptr) {
      std::stringstream ss;
      ss << "Mock `" << typeid(GlobalMock).name() << "` not instantiated yet.";
      throw std::runtime_error(std::move(ss).str());
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

}  // namespace global_mock
#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_GLOBAL_MOCK_H_
