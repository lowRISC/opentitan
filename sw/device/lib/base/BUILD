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
    name = "bitfield",
    srcs = ["bitfield.c"],
    hdrs = ["bitfield.h"],
    deps = [":macros"],
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
    name = "base",
    srcs = [],
    hdrs = ["mmio.h"],
    deprecation = "Please use smaller lib/base targets instead of this one.",
    deps = [
        ":bitfield",
        ":csr",
        ":hardened",
        ":macros",
        ":memory",
        ":multibits",
        ":stdasm",
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
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":mmio",
        ":macros",
    ],
)