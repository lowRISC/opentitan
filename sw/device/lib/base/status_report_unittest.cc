// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <iostream>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/base/status_report_unittest_c.h"

namespace status_list_unittest {
namespace {

// Stack trace stored as a vector for easy access.
std::vector<status_t> StatusList;

// Implement the stack tracing facility.
extern "C" void status_report(status_t code) { StatusList.push_back(code); }

const status_t kExpectedList[] = {
    // The first entry of the list should correspond to the entry pushed by
    //   status_report(OK_STATUS(300));
    // at line 38 to make sure that the report can handle OK statuses as well.
    status_create(absl_status_t::kOk, 0, "", 654321),
    // The next entry of the list should correspond to the TRY() at line 19:
    //   TRY(sudo_god());
    // where the module ID is "psy" and the error is PERMISSION_DENIED().
    status_create(absl_status_t::kPermissionDenied,
                  MAKE_MODULE_ID('p', 's', 'y'), "", 21),
    // The think() function does not use TRY() and instead returns ABORTED()
    // so it creates no entry.
    // The next entry is created by the TRY() at line 34:
    //   TRY(think());
    // where the module ID is "unt" and the error is ABORTED().
    status_create(absl_status_t::kAborted, MAKE_MODULE_ID('u', 'n', 't'), "",
                  41),
    // The last entry is the one we push in the test: this is the error
    // returned by status_report_unittest_c() that comes from think()
    // at line 27 with error code ABORTED() and module ID "thk".
    status_create(absl_status_t::kAborted, MAKE_MODULE_ID('t', 'h', 'k'), "",
                  29),
};

std::string status_to_string(status_t status) {
  int32_t arg;
  const char *message;
  char mod_id[4];
  std::stringstream oss;
  if (status_extract(status, &message, &arg, mod_id)) {
    mod_id[3] = 0;
    oss << message << "(" << arg << ") in " << mod_id;
  } else {
    oss << "Ok(" << arg << ")";
  }
  return oss.str();
}

TEST(StackTrace, Trace) {
  // The unit test exercises the TRY() macro that only works in C code.
  status_t status = status_report_unittest_c();

  // We push the status on the stack just to make checking below easier
  status_report(status);

  EXPECT_EQ(StatusList.size(), ARRAYSIZE(kExpectedList));

  for (size_t i = 0; i < StatusList.size(); i++) {
    EXPECT_EQ(StatusList[i].value, kExpectedList[i].value)
        << "GOT " << status_to_string(StatusList[i]) << ", EXPECTED "
        << status_to_string(kExpectedList[i]);
  }
}

}  // namespace
}  // namespace status_list_unittest
