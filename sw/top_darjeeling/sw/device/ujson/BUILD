# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_test(
    name = "ujson_test",
    srcs = ["//sw/lib/sw/device/ujson:ujson_test.cc"],
    deps = [
        "//sw/lib/sw/device/ujson:test_helpers",
        "//sw/lib/sw/device/ujson:ujson",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "@googletest//:gtest_main",
    ],
)

cc_test(
    name = "example_test",
    srcs = ["//sw/lib/sw/device/ujson:example_test.cc"],
    deps = [
        "//sw/lib/sw/device/ujson:example",
        "//sw/lib/sw/device/ujson:test_helpers",
        "//sw/lib/sw/device/ujson:ujson",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "example_roundtrip",
    srcs = ["//sw/lib/sw/device/ujson:example_roundtrip.c"],
    deps = [
        "//sw/lib/sw/device/ujson:example",
        "//sw/lib/sw/device/base:status",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)
