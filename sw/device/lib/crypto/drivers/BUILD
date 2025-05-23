# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")
load(
    "//rules:cross_platform.bzl",
    "dual_cc_device_library_of",
    "dual_cc_library",
    "dual_inputs",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "verilator_params",
)
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        ":entropy",
        ":rv_core_ibex",
        "//hw/top:aes_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:status",
    ],
)

opentitan_test(
    name = "aes_test",
    srcs = ["aes_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":aes",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "keymgr",
    srcs = ["keymgr.c"],
    hdrs = [
        "keymgr.h",
    ],
    deps = [
        ":entropy",
        ":rv_core_ibex",
        "//hw/top:keymgr_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:hart",
    ],
)

opentitan_test(
    name = "keymgr_test",
    srcs = ["keymgr_test.c"],
    broken = fpga_params(tags = ["broken"]),
    exec_env = dicts.add(
        EARLGREY_TEST_ENVS,
        {
            # FIXME broken in sival ROM_EXT, remove this line when fixed. See #21706.
            "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": "broken",
        },
    ),
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":keymgr",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/testing:keymgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = [
        "kmac.h",
        "//sw/device/lib/crypto/include:datatypes.h",
    ],
    deps = [
        ":entropy",
        ":rv_core_ibex",
        "//hw/top:kmac_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/crypto/impl:status",
    ],
)

dual_cc_library(
    name = "entropy",
    srcs = dual_inputs(
        device = ["entropy.c"],
        host = ["mock_entropy.cc"],
    ),
    hdrs = ["entropy.h"],
    deps = dual_inputs(
        device = [
            "//hw/top:csrng_c_regs",
            "//hw/top:edn_c_regs",
            "//hw/top:entropy_src_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/base:math",
            "//sw/device/lib/base:memory",
        ],
        shared = [
            "//sw/device/lib/crypto/impl:status",
        ],
    ),
)

cc_library(
    name = "entropy_kat",
    srcs = ["entropy_kat.c"],
    hdrs = ["entropy_kat.h"],
    deps = [
        ":entropy",
        "//hw/top:csrng_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
    ],
)

opentitan_test(
    name = "entropy_test",
    srcs = ["entropy_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],  # TODO #16672 test broken by icache
    ),
    deps = [
        ":entropy",
        ":entropy_kat",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:otbn_randomness_impl",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//hw/top:hmac_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
    ],
)

dual_cc_library(
    name = "rv_core_ibex",
    srcs = dual_inputs(
        device = ["rv_core_ibex.c"],
        host = ["mock_rv_core_ibex.cc"],
    ),
    hdrs = dual_inputs(
        shared = ["rv_core_ibex.h"],
    ),
    deps = dual_inputs(
        device = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//hw/top:rv_core_ibex_c_regs",
            "//sw/device/lib/base:abs_mmio",
        ],
    ),
)

opentitan_test(
    name = "rv_core_ibex_test",
    srcs = ["rv_core_ibex_test.c"],
    exec_env = EARLGREY_TEST_ENVS,
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":rv_core_ibex",
        "//hw/top:rv_core_ibex_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:csr",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

cc_library(
    name = "otbn",
    srcs = ["otbn.c"],
    hdrs = ["otbn.h"],
    deps = [
        ":entropy",
        "//hw/top:otbn_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/impl:status",
    ],
)
