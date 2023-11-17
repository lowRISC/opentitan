# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_cryptotest_header")
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "opentitan_test",
    "verilator_params",
)
load("@ot_python_deps//:requirements.bzl", "requirement")

opentitan_test(
    name = "fors_test",
    srcs = ["fors_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:fors",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
    ],
)

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

opentitan_test(
    name = "verify_test_hardcoded",
    srcs = ["verify_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
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

opentitan_test(
    name = "wots_test",
    srcs = ["wots_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:context",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:hash",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:wots",
    ],
)

# Begin KAT test headers: KAT tests are split into multiple targets because the
# large signatures and high number of tests cause timeout and SRAM/ROM_EXT
# space overflow with the full set.

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat0_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat0.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat1_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat1.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat2_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat2.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat3_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat3.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat4_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat4.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat5_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat5.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat6_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat6.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat7_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat7.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat8_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat8.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

autogen_cryptotest_header(
    name = "sphincsplus_shake_128s_simple_testvectors_kat9_header",
    hjson = "//sw/device/tests/crypto/testvectors/sphincsplus_kat:sphincsplus_shake_128s_simple_testvectors_kat9.hjson",
    template = ":sphincsplus_shake_128s_simple_testvectors.h.tpl",
    tool = ":sphincsplus_set_testvectors",
)

opentitan_test(
    name = "verify_test_kat0",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat0_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat1",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat1_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat2",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat2_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat3",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat3_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat4",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat4_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat5",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat5_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat6",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat6_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat7",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat7_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat8",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat8_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)

opentitan_test(
    name = "verify_test_kat9",
    srcs = ["verify_test.c"],
    exec_env = {
        # Test set is too large for Verilator or as ROM_EXT
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_hyper310_test_rom": None,
    },
    deps = [
        ":sphincsplus_shake_128s_simple_testvectors_kat9_header",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/runtime:ibex",
        "//sw/device/lib/testing:profile",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
    ],
)
