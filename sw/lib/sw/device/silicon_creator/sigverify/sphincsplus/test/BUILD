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
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/test/utils:profile",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:verify",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "fors_test",
    srcs = ["fors_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:context",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:fors",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:hash",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "wots_test",
    srcs = ["wots_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:context",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:hash",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:wots",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/top_darjeeling/sw/device/runtime:print",
    ],
)
