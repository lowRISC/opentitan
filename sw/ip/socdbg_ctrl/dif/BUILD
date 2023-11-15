# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "api",
    srcs = glob(
        include = ["*.h"],
        exclude = ["*_unittest.h"],
    ),
)

filegroup(
    name = "headers",
    srcs = glob(
        include = ["**/*.h"],
        exclude = ["**/*_unittest.h"],
    ),
)

filegroup(
    name = "sources",
    srcs = glob(["**/*.c"]),
)

filegroup(
    name = "test_headers",
    srcs = glob(["**/*_unittest.h"]),
)

filegroup(
    name = "test_sources",
    srcs = glob(["**/*_unittest.cc"]),
)
