# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:linker.bzl", "ld_library")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "coverage",
    srcs = ["coverage_none.c"],
    hdrs = ["coverage.h"],
)

cc_library(
    name = "status",
    srcs = ["status.c"],
    hdrs = ["status.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
    ],
)

cc_library(
    name = "check",
    hdrs = ["check.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":status",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:base",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
    ],
)

ld_library(
    name = "linker_script",
    script = "ottf.ld",
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
        "//sw/device:info_sections",
    ],
)

# This target provides start files without providing the full OTTF, and can be used
# to bootstrap post-ROM execution without pulling in the full OTTF.
#
# The binary target must provide a `noreturn void _ottf_main(void)` function that
# this library will call.
cc_library(
    name = "ottf_start",
    srcs = [
        "ottf_isrs.S",
        "ottf_isrs.c",
        "ottf_start.S",
    ],
    hdrs = [
        "ottf_isrs.h",
        "ottf_macros.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":linker_script",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crt",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/silicon_creator/lib:manifest_size",
    ],
)

cc_library(
    name = "ottf_test_config",
    hdrs = [
        "ottf_test_config.h",
    ],
)

cc_library(
    name = "ottf_main",
    srcs = ["ottf_main.c"],
    hdrs = ["ottf_main.h"],
    # FIXME: Temporary hack to allow us to #include the version in //third_party.
    # To be removed once Meson is removed.
    # https://github.com/lowRISC/opentitan/issues/11743
    local_defines = ["FREERTOS_IS_BAZEL"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":check",
        ":coverage",
        ":freertos_port",
        ":ottf_start",
        ":ottf_test_config",
        ":status",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//third_party/freertos",
        "@manufacturer_test_hooks//:test_hooks",
    ],
    # `:ottf` depends on `:ottf_start`, but `:ottf_start` gets its main function from
    # `:ottf`. Thus we need to include all of the objects in `:ottf` unconditionally
    # so that the linker can find the symbol later.
    alwayslink = True,
)

cc_library(
    name = "freertos_config",
    hdrs = ["FreeRTOSConfig.h"],
    # FreeRTOS sources don't follow our project's include-path standard,
    # and just include via the bare filename.
    includes = ["."],
)

cc_library(
    name = "freertos_port",
    srcs = [
        "freertos_hooks.c",
        "freertos_port.S",
        "freertos_port.c",
    ],
    # FIXME: Temporary hack to allow us to #include the version in //third_party.
    # To be removed once Meson is removed.
    # https://github.com/lowRISC/opentitan/issues/11743
    local_defines = ["FREERTOS_IS_BAZEL"],
    deps = [
        ":check",
        ":freertos_config",
        ":ottf_start",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//third_party/freertos",
    ],
    # This library provides FreeRTOS hooks that are required for FreeRTOS to link,
    # but FreeRTOS (currently) does not depend on this target. Therefore, we need
    # to include all of the symbols from this object in the link so that they are
    # found during linking.
    alwayslink = True,
)
