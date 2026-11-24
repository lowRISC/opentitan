# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:dicts.bzl", "dicts")
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_CW340_TEST_ENVS",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "OPENTITAN_CPU",
    "opentitan_test",
)
load("//rules/coverage:asm.bzl", "asm_library_with_coverage")
load("//rules:otbn.bzl", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "target",
    srcs = ["target.c"],
    hdrs = ["target.h"],
)

cc_test(
    name = "host_unittest",
    srcs = ["host_unittest.cc"],
    deps = [
        ":target",
        "@googletest//:gtest_main",
    ],
)

otbn_sim_test(
    name = "otbn_simtest",
    srcs = ["target_otbn.s"],
    testcase = "otbn_simtest.hjson",
)

opentitan_test(
    name = "ottf_functest",
    srcs = ["ottf_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_CW340_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        ":target",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

asm_library_with_coverage(
    name = "target_asm",
    srcs = ["target_asm.S"],
    hdrs = ["target.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        "//sw/device/lib/coverage:api_asm",
    ],
)

opentitan_test(
    name = "asm_functest",
    srcs = ["ottf_functest.c"],
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        EARLGREY_CW340_TEST_ENVS,
        {
            "//hw/top_earlgrey:silicon_creator": None,
        },
    ),
    deps = [
        ":target_asm",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
