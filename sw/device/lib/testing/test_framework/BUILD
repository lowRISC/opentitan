# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")

package(default_visibility = ["//visibility:public"])

# TODO use more specific targets to avoid unnecesary dependencies
# https://github.com/lowRISC/opentitan/issues/9098
cc_library(
    name = "test_framework",
    srcs = [
        "test_coverage_none.c",
        "test_status.c",
    ],
    hdrs = [
        "test_coverage.h",
        "test_status.h",
        "//sw/device/lib/testing:check",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
    ],
)

# TODO(lowRISC/opentitan#7972): clean up check.h after completing the
# migration to bazel.
cc_library(
    name = "check",
    hdrs = [
        "test_status.h",
        "//sw/device/lib/testing:check",
    ],
    visibility = ["//visibility:private"],
)

cc_library(
    name = "freertos_config",
    hdrs = [
        "FreeRTOSConfig.h",
    ],
    # FreeRTOS sources don't follow our project's include-path standard,
    # and just include via the bare filename.
    includes = ["."],
    deps = [
        "//sw/device/lib/arch:device",
    ],
)

cc_library(
    name = "freertos_port",
    srcs = [
        "freertos_hooks.c",
        "freertos_port.S",
        "freertos_port.c",
    ],
    hdrs = [
        "ottf_macros.h",
    ],
    deps = [
        ":check",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib:irq",
        "//sw/device/lib/dif:rv_timer",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/vendor/freertos_freertos_kernel:kernel",
    ],
)

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
    copts = [
        "-nostdlib",
        "-ffreestanding",
    ],
    linkopts = [
        "-T $(location ottf.ld)",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "ottf.ld",
        "//hw/top_earlgrey/sw/autogen:linker_script",
        "//sw/device:info_sections",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crt",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/silicon_creator/lib:manifest_size",
    ],
)

cc_library(
    name = "ottf",
    srcs = [
        "ottf.c",
    ],
    hdrs = [
        "ottf.h",
        "//sw/device/lib/testing:check",
    ],
    linkopts = [
        # Make the linker keep resolving references between these
        # targets until satisfied.
        "-Wl,--start-group",
        "$(location :freertos_port)",
        "$(location //sw/device/lib:irq)",
        "$(location //sw/vendor/freertos_freertos_kernel:kernel)",
        "-Wl,--end-group",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":freertos_port",
        ":test_framework",
        "//sw/device/lib:irq",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/vendor/freertos_freertos_kernel:kernel",
    ],
)
