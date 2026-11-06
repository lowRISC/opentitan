# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

otbn_sim_test(
    name = "urnd_ctrl_test",
    srcs = [
        "urnd_ctrl_test.s",
    ],
)

# Same program as a linkable binary.
otbn_binary(
    name = "urnd_ctrl",
    srcs = [
        "urnd_ctrl_test.s",
    ],
)
