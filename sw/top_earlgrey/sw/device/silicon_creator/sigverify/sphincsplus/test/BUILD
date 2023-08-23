# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load(
    "//rules:opentitan_test.bzl",
    "opentitan_functest",
    "verilator_params",
)

opentitan_functest(
    name = "verify_test_hardcoded",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus/test:verify_test.c",
    ],
    verilator = verilator_params(
        timeout = "eternal",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/ip/base/test/utils:profile",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:verify",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus/test:sphincsplus_shake_128s_simple_testvectors_hardcoded_header",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "fors_test",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus/test:fors_test.c",
    ],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:context",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:fors",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:hash",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)

opentitan_functest(
    name = "wots_test",
    srcs = [
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus/test:wots_test.c",
    ],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/runtime:ibex",
        "//sw/lib/sw/device/runtime:log",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:context",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:hash",
        "//sw/lib/sw/device/silicon_creator/sigverify/sphincsplus:wots",
        "//sw/top_earlgrey/sw/device/runtime:print",
    ],
)
