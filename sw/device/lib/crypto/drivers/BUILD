# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//hw/ip/aes/data:aes_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/device/lib/crypto/impl:status",
    ],
)

opentitan_functest(
    name = "aes_test",
    srcs = ["aes_test.c"],
    verilator = verilator_params(
        timeout = "long",
    ),
    deps = [
        ":aes",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/device/lib/crypto/impl:status",
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
        "//hw/ip/kmac/data:kmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "entropy",
    srcs = ["entropy.c"],
    hdrs = ["entropy.h"],
    deps = [
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/ip/edn/data:edn_regs",
        "//hw/ip/entropy_src/data:entropy_src_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "entropy_kat",
    srcs = ["entropy_kat.c"],
    hdrs = ["entropy_kat.h"],
    deps = [
        ":entropy",
        "//hw/ip/csrng/data:csrng_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/lib/sw/device/base:status",
        "//sw/lib/sw/device/runtime:log",
    ],
)

opentitan_functest(
    name = "entropy_test",
    srcs = ["entropy_test.c"],
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],  # TODO #16672 test broken by icache
    ),
    deps = [
        ":entropy",
        ":entropy_kat",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/dif:otbn",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:otbn_randomness_impl",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/top_earlgrey/sw/dif:otbn",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//hw/ip/hmac/data:hmac_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:memory",
        "//sw/device/lib/crypto/impl:status",
    ],
)

cc_library(
    name = "otbn",
    srcs = ["otbn.c"],
    hdrs = ["otbn.h"],
    deps = [
        "//hw/ip/otbn/data:otbn_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/lib/sw/device/base:abs_mmio",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/device/lib/crypto/impl:status",
    ],
)
