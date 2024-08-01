# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Build configuration for CoreMark test."""

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "opentitan_test",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "core_portme",
    hdrs = ["core_portme.h"],
    includes = ["."],
)

opentitan_test(
    name = "coremark_test",
    srcs = [
        "core_portme.c",
        "cvt.c",
        "ee_printf.c",
    ],
    copts = [
        "-Wno-implicit-fallthrough",
        "-Wno-strict-prototypes",
        "-Wno-implicit-int-conversion",
        "-Wno-sign-conversion",
        "-Wno-shorten-64-to-32",
        "-DITERATIONS=12",
        "-DPERFORMANCE_RUN=1",
        "-DTOTAL_DATA_SIZE=2000",
        "-DMAIN_HAS_NOARGC=1",
    ],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    ),
    verilator = verilator_params(
        timeout = "eternal",
        # This test can take > 60 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
    ),
    deps = [
        ":core_portme",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_start",
        "//sw/device/lib/testing/test_framework:ottf_test_config",
        "//sw/device/lib/testing/test_framework:status",
        "@coremark//:coremark_lib",
    ],
)
