# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "mldsa_test_utils",
    srcs = [
        "mldsa_test_utils.c",
    ],
    hdrs = [
        "mldsa_test_utils.h",
    ],
    deps = [
        "//sw/device/lib/runtime:log",
    ],
)

cc_library(
    name = "mldsa_testvectors",
    srcs = ["mldsa_testvectors.c"],
    hdrs = ["mldsa_testvectors.h"],
    deps = [
        "//third_party/embedpqc:mldsa44_tiny",
    ],
)

opentitan_test(
    name = "mldsa44_tiny_test",
    srcs = ["mldsa44_tiny_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    deps = [
        ":mldsa_test_utils",
        ":mldsa_testvectors",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//third_party/embedpqc:mldsa44_tiny",
        "//third_party/embedpqc/ports:mldsa44_tiny_caller",
    ],
)
