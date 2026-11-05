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
    "dv_params",
    "fpga_params",
    "opentitan_test",
    "qemu_params",
    "silicon_params",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

VTS_CTS_EXEC_ENVS = dicts.add(
    EARLGREY_TEST_ENVS,
    EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
    {
        "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
    },
)

opentitan_test(
    name = "aes_vts_cts_test",
    srcs = ["aes_vts_cts_test.c"],
    dv = dv_params(
        tags = ["broken"],
    ),
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        tags = ["broken"],
    ),
    qemu = qemu_params(
        tags = ["broken"],
    ),
    run_in_ci = [],
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
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
    dv = dv_params(
        tags = ["broken"],
    ),
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        tags = ["broken"],
    ),
    qemu = qemu_params(
        tags = ["broken"],
    ),
    run_in_ci = [],
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
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
    dv = dv_params(
        tags = ["broken"],
    ),
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        tags = ["broken"],
    ),
    qemu = qemu_params(
        tags = ["broken"],
    ),
    run_in_ci = [],
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
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
    dv = dv_params(
        tags = ["broken"],
    ),
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        timeout = "long",
        tags = ["broken"],
    ),
    qemu = qemu_params(
        tags = ["broken"],
    ),
    run_in_ci = [],
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "eternal",
        tags = [
            "broken",
            "manual",
        ],
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:rsa",
        "//sw/device/lib/crypto/impl:sha1",
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
    dv = dv_params(
        tags = ["broken"],
    ),
    exec_env = VTS_CTS_EXEC_ENVS,
    fpga = fpga_params(
        tags = ["broken"],
    ),
    qemu = qemu_params(
        tags = ["broken"],
    ),
    run_in_ci = [],
    silicon = silicon_params(
        tags = ["broken"],
    ),
    verilator = verilator_params(
        timeout = "long",
        tags = ["broken"],
    ),
    deps = [
        "//sw/device/lib/base:macros",
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/impl:config",
        "//sw/device/lib/crypto/impl:ecc_curve25519",
        "//sw/device/lib/crypto/impl:ecc_p256",
        "//sw/device/lib/crypto/impl:ecc_p384",
        "//sw/device/lib/crypto/impl:hmac",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:sha1",
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
    tags = [
        "broken",
        "manual",
    ],
    tests = [
        "aes_gcm_vts_cts_test",
        "aes_vts_cts_test",
        "ecc_mac_vts_cts_test",
        "rsa_vts_cts_test",
        "tdes_vts_cts_test",
    ],
)
