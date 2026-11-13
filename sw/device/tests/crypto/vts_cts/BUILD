# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

VTS_CTS_EXEC_ENVS = dicts.add(
    dicts.omit(
        EARLGREY_TEST_ENVS,
        [
            "//hw/top_earlgrey:sim_dv",
            "//hw/top_earlgrey:sim_verilator",
        ],
    ),
    EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    {
        "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
    },
)

opentitan_test(
    name = "aes_vts_cts_test",
    srcs = ["aes_vts_cts_test.c"],
    exec_env = VTS_CTS_EXEC_ENVS,
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "tdes_vts_cts_test",
    srcs = ["tdes_vts_cts_test.c"],
    exec_env = VTS_CTS_EXEC_ENVS,
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/impl:tdes",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "aes_gcm_vts_cts_test",
    srcs = ["aes_gcm_vts_cts_test.c"],
    exec_env = VTS_CTS_EXEC_ENVS,
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:aes_gcm",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "rsa_vts_cts_test",
    srcs = ["rsa_vts_cts_test.c"],
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "ecc_mac_vts_cts_test",
    srcs = ["ecc_mac_vts_cts_test.c"],
    exec_env = VTS_CTS_EXEC_ENVS,
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:hkdf",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:key_transport",
        "//sw/device/lib/crypto/impl:sha2",
        "//sw/device/lib/crypto/impl:status",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

test_suite(
    name = "vts_cts_test_suite",
    tests = [
        "aes_gcm_vts_cts_test",
        "aes_vts_cts_test",
        "ecc_mac_vts_cts_test",
        "rsa_vts_cts_test",
        "tdes_vts_cts_test",
    ],
)
