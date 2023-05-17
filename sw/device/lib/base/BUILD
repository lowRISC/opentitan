# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")
load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "global_mock",
    hdrs = ["global_mock.h"],
)

cc_library(
    name = "stdasm",
    hdrs = ["stdasm.h"],
)

cc_library(
    name = "macros",
    hdrs = [
        "adv_macros.h",
        "macros.h",
    ],
)

cc_library(
    name = "math_polyfills",
    srcs = ["math_builtins.c"],

    # This library defines polyfills, so we need to ensure LLVM doesn't make
    # the polyfills call themselves.
    copts = ["-fno-builtin"],
    visibility = ["//visibility:private"],
    deps = [":macros"],
)

alias(
    name = "math_builtins",
    actual = select({
        "//sw/device:measure_coverage_on_target": "//sw/device:nothing",
        "//conditions:default": ":math_polyfills",
    }),
    visibility = ["//visibility:private"],
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
    deps = [
        ":macros",
    ],
)

opentitan_functest(
    name = "memory_perftest",
    srcs = ["memory_perftest.c"],
    cw310 = cw310_params(
        tags = [
            "flaky",
            "manual",
        ],
    ),
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    targets = ["cw310_test_rom"],
    deps = [
        ":macros",
        ":memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_test(
    name = "memory_unittest",
    srcs = ["memory_unittest.cc"],
    deps = [
        ":memory",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "hardened",
    srcs = ["hardened.c"],
    hdrs = [
        "hardened.h",
        "hardened_asm.h",
    ],
    deps = [
        ":macros",
        ":memory",
        ":stdasm",
    ],
)

cc_test(
    name = "hardened_unittest",
    srcs = ["hardened_unittest.cc"],
    deps = [
        ":hardened",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "random_order",
    srcs = ["random_order.c"],
    hdrs = ["random_order.h"],
    deps = [":bitfield"],
)

cc_library(
    name = "hardened_memory",
    srcs = ["hardened_memory.c"],
    hdrs = ["hardened_memory.h"],
    deps = [
        ":hardened",
        ":macros",
        ":memory",
        ":random_order",
    ],
)

cc_test(
    name = "hardened_memory_unittest",
    srcs = ["hardened_memory_unittest.cc"],
    deps = [
        ":hardened_memory",
        ":random_order",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "csr",
    srcs = dual_inputs(
        host = ["//sw/device/silicon_creator/lib/base:mock_csr.cc"],
    ),
    hdrs = dual_inputs(
        host = [
            "//sw/device/silicon_creator/lib/base:mock_csr.h",
        ],
        shared = [
            "csr.h",
            "csr_registers.h",
        ],
    ),
    deps = dual_inputs(
        host = [
            "global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            ":macros",
            ":stdasm",
        ],
    ),
)

cc_test(
    name = "mock_csr_unittest",
    srcs = ["//sw/device/silicon_creator/lib/base:mock_csr_test.cc"],
    deps = [
        ":csr",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "multibits",
    hdrs = [
        "multibits.h",
        "multibits_asm.h",
    ],
)

dual_cc_library(
    name = "mmio",
    srcs = dual_inputs(
        host = ["mock_mmio.cc"],
        # NOTE: mmio.c is shared because it provides mmio_memcpy and friends.
        shared = ["mmio.c"],
    ),
    hdrs = dual_inputs(
        host = [
            "mock_mmio.h",
            "mock_mmio_test_utils.h",
        ],
        shared = ["mmio.h"],
    ),
    deps = dual_inputs(
        host = [
            "@googletest//:gtest",
        ],
        shared = [
            ":bitfield",
            ":macros",
            ":memory",
        ],
    ),
)

cc_test(
    name = "mmio_unittest",
    srcs = ["mock_mmio_test.cc"],
    deps = [
        ":mmio",
        "@googletest//:gtest_main",
    ],
)

dual_cc_library(
    name = "abs_mmio",
    srcs = dual_inputs(
        device = ["abs_mmio.c"],
        host = ["mock_abs_mmio.cc"],
    ),
    hdrs = dual_inputs(
        host = [
            "mock_abs_mmio.h",
        ],
        shared = ["abs_mmio.h"],
    ),
    deps = dual_inputs(
        host = [
            "global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            ":mmio",
            ":macros",
        ],
    ),
)

cc_library(
    name = "status",
    srcs = ["status.c"],
    hdrs = ["status.h"],
    deps = [
        ":bitfield",
        ":macros",
        "//sw/device/lib/base/internal:status",
        "//sw/device/lib/dif:base",
        "//sw/device/silicon_creator/lib:error",
    ],
)

cc_test(
    name = "status_unittest",
    srcs = ["status_unittest.cc"],
    deps = [
        ":status",
        "@googletest//:gtest_main",
    ],
)
