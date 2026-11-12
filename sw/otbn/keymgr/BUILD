# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary", "otbn_library")

package(default_visibility = ["//visibility:public"])

otbn_library(
    name = "keymgr",
    srcs = [
        "keymgr.s",
    ],
)

otbn_binary(
    name = "keymgr_test",
    srcs = [
        # do not sort
        "keymgr.s",
        "keymgr_test.s",
    ],
)
