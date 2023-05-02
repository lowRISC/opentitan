# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:ujson.bzl", "ujson_rust")
load("//rules:cross_platform.bzl", "dual_cc_device_library_of")

cc_library(
    name = "ujson",
    srcs = ["ujson.c"],
    hdrs = [
        "ujson.h",
        "ujson_derive.h",
        "ujson_rust.h",
    ],
    deps = [
        ":private_status",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:print",
        dual_cc_device_library_of("//sw/device/silicon_creator/lib:crc32"),
    ],
)

cc_library(
    name = "private_status",
    srcs = [
        "private_status.c",
        "ujson.h",
        "ujson_derive.h",
    ],
    hdrs = ["private_status.h"],
    visibility = ["//visibility:private"],
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:status",
    ],
)

cc_library(
    name = "test_helpers",
    hdrs = ["test_helpers.h"],
)

cc_test(
    name = "ujson_test",
    srcs = ["ujson_test.cc"],
    deps = [
        ":test_helpers",
        ":ujson",
        "//sw/device/lib/base:status",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "example",
    srcs = ["example.c"],
    hdrs = ["example.h"],
    deps = [":ujson"],
)

cc_test(
    name = "example_test",
    srcs = ["example_test.cc"],
    deps = [
        ":example",
        ":test_helpers",
        ":ujson",
        "//sw/device/lib/base:status",
        "@googletest//:gtest_main",
    ],
)

cc_binary(
    name = "example_roundtrip",
    srcs = ["example_roundtrip.c"],
    deps = [
        ":example",
        "//sw/device/lib/base:status",
    ],
)
