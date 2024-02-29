# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
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
        "//sw/device/lib/crypto/impl/ecc:ecdsa_p256",
        "//sw/device/lib/crypto/impl/ecc:p256_common",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
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
        "//sw/device/lib/crypto/impl:hash",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl/sha2:sha256",
        "//sw/device/lib/crypto/impl/sha2:sha512",
        "//sw/device/lib/crypto/include:datatypes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
    ],
)

cc_library(
    name = "aes_sca",
    srcs = ["aes_sca.c"],
    hdrs = ["aes_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aes",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:aes",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:aes_sca_commands",
    ],
)

cc_library(
    name = "ibex_fi",
    srcs = ["ibex_fi.c"],
    hdrs = [
        "ibex_fi.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:rv_core_ibex",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:ibex_fi_commands",
    ],
)

cc_library(
    name = "kmac_sca",
    srcs = ["kmac_sca.c"],
    hdrs = [
        "kmac_sca.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:kmac_sca_commands",
    ],
)

cc_library(
    name = "prng_sca",
    srcs = ["prng_sca.c"],
    hdrs = ["prng_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/tests/crypto/cryptotest/json:prng_sca_commands",
    ],
)

cc_library(
    name = "sha3_sca",
    srcs = ["sha3_sca.c"],
    hdrs = [
        "sha3_sca.h",
        "status.h",
    ],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:kmac",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:prng",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:sha3_sca_commands",
    ],
)

cc_library(
    name = "trigger_sca",
    srcs = ["trigger_sca.c"],
    hdrs = ["trigger_sca.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/sca/lib:sca",
        "//sw/device/tests/crypto/cryptotest/json:trigger_sca_commands",
    ],
)

opentitan_binary(
    name = "firmware",
    testonly = True,
    srcs = [":firmware.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_test_rom",
    ],
    deps = [
        ":aes",
        ":aes_sca",
        ":ecdsa",
        ":hash",
        ":ibex_fi",
        ":kmac_sca",
        ":prng_sca",
        ":sha3_sca",
        ":trigger_sca",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
        "//sw/device/tests/crypto/cryptotest/json:commands",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
        "//sw/device/tests/crypto/cryptotest/json:ibex_fi_commands",
    ],
)

opentitan_test(
    name = "chip_pen_test",
    srcs = [":firmware.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
    },
    silicon_owner = silicon_params(
        tags = ["broken"],
    ),
    deps = [
        ":aes",
        ":aes_sca",
        ":ecdsa",
        ":hash",
        ":ibex_fi",
        ":kmac_sca",
        ":prng_sca",
        ":sha3_sca",
        ":trigger_sca",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
        "//sw/device/tests/crypto/cryptotest/json:commands",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
        "//sw/device/tests/crypto/cryptotest/json:ibex_fi_commands",
    ],
)
