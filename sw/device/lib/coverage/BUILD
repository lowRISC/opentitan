# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:linker.bzl", "ld_library")
load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")
load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "api",
    hdrs = ["api.h"],
    deps = [
        "//sw/device/lib/base:macros",
    ],
)

cc_library(
    name = "api_asm",
    hdrs = ["api_asm.h"],
    deps = [
        ":api",
    ],
)

cc_library(
    name = "printer",
    srcs = ["printer.c"],
    hdrs = ["printer.h"],
    features = ["-coverage"],
    deps = [
        "//sw/device/lib/base:crc32",
        "//sw/device/lib/base:macros",
    ],
    alwayslink = True,  # replacing weak symbol
)

cc_library(
    name = "ottf_runtime_real",
    srcs = ["ottf_runtime.c"],
    features = ["-coverage"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":printer",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_console",
    ],
    alwayslink = True,  # replacing weak symbol
)

cc_library(
    name = "ottf_runtime_skip",
    srcs = ["ottf_runtime_skip.c"],
    features = ["-coverage"],
    deps = [
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_console",
    ],
    alwayslink = True,  # replacing weak symbol
)

alias(
    name = "ottf_runtime",
    actual = select({
        "//rules/coverage:instrumented": ":ottf_runtime_real",
        "//rules/coverage:enabled": ":ottf_runtime_skip",
        "//conditions:default": "//sw/device:nothing",
    }),
)

ld_library(
    name = "coverage_sections",
    includes = [
        "bss.ld",
        "info.ld",
        "rodata.ld",
    ],
)
