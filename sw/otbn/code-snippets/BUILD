# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "barrett384",
    srcs = [
        "barrett384.s",
    ],
)

otbn_binary(
    name = "err_test",
    srcs = [
        "err_test.s",
    ],
)
