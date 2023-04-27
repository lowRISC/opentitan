# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_cryptotest_header")
load(
    "//rules:opentitan_test.bzl",
    "opentitan_functest",
    "verilator_params",
)
load("@ot_python_deps//:requirements.bzl", "requirement")

py_binary(
    name = "sphincsplus_set_testvectors",
    srcs = ["sphincsplus_set_testvectors.py"],
    deps = [
        requirement("hjson"),
        requirement("mako"),
    ],
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_hardcoded_header",
    hjson = "//sw/device/tests/crypto/testvectors:sphincsplus_shake_128s_simple_testvectors_hardcoded",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

opentitan_functest(
    name = "verify_test_hardcoded",
    srcs = ["verify_test.c"],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_hardcoded_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_functest(
    name = "fors_test",
    srcs = ["fors_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:fors",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
    ],
)

opentitan_functest(
    name = "wots_test",
    srcs = ["wots_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:wots",
    ],
)
