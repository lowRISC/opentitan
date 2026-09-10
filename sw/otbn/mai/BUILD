# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_sim_test(
    name = "mai_test",
    srcs = [
        "mai_test.s",
    ],
    testcase = "mai_test.hjson",
)

# Same program as a linkable binary, for use as a top-level test (otbn_mai_test).
otbn_binary(
    name = "mai_tlt_test",
    srcs = [
        "mai_test.s",
    ],
)
