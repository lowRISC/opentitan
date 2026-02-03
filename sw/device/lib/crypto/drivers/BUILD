# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_cryptolib_build_info")
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
    "qemu_params",
    "verilator_params",
)
load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)

autogen_cryptolib_build_info(name = "cryptolib_build_info")

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        ":entropy",
        ":rv_core_ibex",
        "//hw/ip/aes/data:aes_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:crc32",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
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
        ":rv_core_ibex",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

# Run with --config=fuzztest
cc_test(
    name = "aes_fuzztest",
    srcs = ["aes_fuzztest.cc"],
    deps = [
        ":aes",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/silicon_creator/testing:rom_test",
        "@fuzztest//fuzztest",
        "@fuzztest//fuzztest:fuzztest_gtest_main",
        "@googletest//:gtest",
    ],
)

# Run via Centipede - BROKEN
cc_binary(
    name = "aes_fuzztest_binary",
    testonly = True,
    srcs = ["aes_fuzztest.cc"],
    deps = [
        ":aes",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/silicon_creator/testing:rom_test",
        "@fuzztest//fuzztest",
        "@fuzztest//fuzztest:fuzztest_gtest_main",
        "@googletest//:gtest",
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
        "//hw/ip/keymgr/data:keymgr_c_regs",
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
            "//hw/top_earlgrey:sim_qemu_sival_rom_ext": "qemu_broken",
        },
    ),
    qemu_broken = qemu_params(tags = ["broken"]),
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
        "//hw/ip/kmac/data:kmac_c_regs",
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
            "//hw/ip/csrng/data:csrng_c_regs",
            "//hw/ip/edn/data:edn_c_regs",
            "//hw/ip/entropy_src/data:entropy_src_c_regs",
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
        "//hw/ip/csrng/data:csrng_c_regs",
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
        ":entropy",
        "//hw/ip/hmac/data:hmac_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:crc32",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/runtime:ibex",
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
            "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:csr",
            "//sw/device/lib/base:macros",
        ],
        shared = [
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/crypto/impl:status",
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
        "//hw/ip/rv_core_ibex/data:rv_core_ibex_c_regs",
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
        "//hw/ip/otbn/data:otbn_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:bitfield",
        "//sw/device/lib/base:crc32",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:random_order",
        "//sw/device/lib/crypto/impl:status",
    ],
)
