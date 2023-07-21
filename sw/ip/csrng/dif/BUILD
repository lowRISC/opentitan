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
        exclude = [
            "**/*_unittest.h",
            "shared/*.h",
        ],
    ),
)

filegroup(
    name = "sources",
    srcs = glob(
        include = ["**/*.c"],
        exclude = ["shared/*.c"],
    ),
)

filegroup(
    name = "shared_api",
    srcs = glob(["shared/dif_csrng_shared.h"]),
)

filegroup(
    name = "shared_headers",
    srcs = glob(
        include = ["shared/*.h"],
        exclude = ["shared/*_unittest.h"],
    ),
)

filegroup(
    name = "shared_sources",
    srcs = glob(["shared/*.c"]),
)

filegroup(
    name = "test_headers",
    srcs = glob(["**/*_unittest.h"]),
)

filegroup(
    name = "test_sources",
    srcs = glob(["**/*_unittest.cc"]),
)
