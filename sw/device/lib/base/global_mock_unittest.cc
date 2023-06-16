// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/global_mock.h"

#include "gtest/gtest.h"

namespace global_mock_test {

// This is a regression test for a casting bug in `GlobalMock<T>`. The
// `GlobalMock()` constructor erroneously cast `this` to `T*` before the `T`
// object was constructed.
//
// This is what UBSan has to say when `GlobalMock`'s constructor casts `this` to
// `MockFoo*`:
//     runtime error: downcast of address 0x7ffdb2a52900 which does not point to
//     an object of type 'MockFoo'
TEST(GlobalMockTest, DowncastHygieneRegressionTest) {
  class MockFoo : public global_mock::GlobalMock<MockFoo> {
   public:
    int value() { return value_; }

   private:
    int value_ = 42;
  };

  MockFoo foo;
  MockFoo &foo_ref = global_mock::GlobalMock<MockFoo>::Instance();
  ASSERT_EQ(foo_ref.value(), 42);
}

}  // namespace global_mock_test
