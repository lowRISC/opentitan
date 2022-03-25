# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

cc_library(
    name = "stdasm",
    hdrs = ["stdasm.h"],
)

cc_library(
    name = "macros",
    hdrs = ["macros.h"],
)

cc_library(
    name = "math_builtins",
    srcs = ["math_builtins.c"],

    # This library defines polyfills, so we need to ensure LLVM doesn't make
    # the polyfills call themselves.
    copts = ["-fno-builtin"],
    visibility = ["//visibility:private"],
    deps = [":macros"],
)

cc_test(
    name = "math_builtins_unittest",
    srcs = ["math_builtins_unittest.cc"],
    deps = [
        ":bitfield",
        ":math_builtins",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "math",
    srcs = ["math.c"],
    hdrs = ["math.h"],
    deps = [":math_builtins"],
)

cc_test(
    name = "math_unittest",
    srcs = ["math_unittest.cc"],
    deps = [
        ":math",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "bitfield",
    srcs = ["bitfield.c"],
    hdrs = ["bitfield.h"],
    deps = [
        ":macros",
        ":math",
    ],
)

cc_library(
    name = "memory",
    srcs = ["memory.c"],
    hdrs = ["memory.h"],

    # This library defines memcpy(), so we can't have LLVM rewriting memcpy
    # into a call to itself.
    copts = ["-fno-builtin"],
)

cc_library(
    name = "hardened",
    srcs = ["hardened.c"],
    hdrs = ["hardened.h"],
    deps = [
        ":macros",
        ":memory",
        ":stdasm",
    ],
)

cc_test(
    name = "hardened_unittest",
    srcs = ["hardened_unittest.cc"],
    defines = [
        "OT_OFF_TARGET_TEST",
    ],
    deps = [
        ":hardened",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "csr",
    hdrs = [
        "csr.h",
        "csr_registers.h",
    ],
    deps = [":stdasm"],
)

cc_library(
    name = "multibits",
    hdrs = [
        "multibits.h",
        "multibits_asm.h",
    ],
)

cc_library(
    name = "mmio",
    srcs = ["mmio.c"],
    hdrs = ["mmio.h"],
    deps = [
        ":bitfield",
        ":macros",
        ":memory",
    ],
)

cc_library(
    name = "abs_mmio",
    srcs = ["abs_mmio.c"],
    hdrs = ["abs_mmio.h"],
    deps = [
        ":macros",
        ":mmio",
    ],
)
