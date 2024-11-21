# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:aes",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
    ],
)

cc_library(
    name = "ecdsa",
    srcs = ["ecdsa.c"],
    hdrs = ["ecdsa.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl/ecc:p256",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
    ],
)

cc_library(
    name = "ecdh",
    srcs = ["ecdh.c"],
    hdrs = ["ecdh.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:ecc",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdh_commands",
    ],
)

cc_library(
    name = "drbg",
    srcs = ["drbg.c"],
    hdrs = ["drbg.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:drbg_commands",
    ],
)

cc_library(
    name = "hash",
    srcs = ["hash.c"],
    hdrs = ["hash.h"],
    deps = [
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hmac_commands",
    ],
)

cc_library(
    name = "sphincsplus",
    srcs = ["sphincsplus.c"],
    hdrs = ["sphincsplus.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
        "//sw/device/tests/crypto/cryptotest/json:sphincsplus_commands",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = ["kmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl:mac",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:kmac_commands",
    ],
)

FIRMWARE_DEPS = [
    ":aes",
    ":drbg",
    ":ecdh",
    ":ecdsa",
    ":hash",
    ":hmac",
    ":kmac",
    ":sphincsplus",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",
    "//hw/top_earlgrey/sw/autogen:top_earlgrey",

    # Include all JSON commands.
    "//sw/device/tests/crypto/cryptotest/json:commands",
]

opentitan_binary(
    name = "firmware",
    testonly = True,
    srcs = [":firmware.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw340",
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext",
    ],
    deps = FIRMWARE_DEPS,
)

opentitan_test(
    name = "chip_pen_test",
    srcs = [":firmware.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
    },
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    deps = FIRMWARE_DEPS,
)
