# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "smoke_test",
    srcs = [
        "smoke_test.s",
    ],
    args = [
        "--defsym",
        "deterministic=1",
    ],
)
